import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorSecurity

/-! A native component that terminates on actual sampled-seed layouts but
loops on a malformed layout. Its typed composition proves no global native
termination assumption is being reintroduced. Identity output is deliberate:
this tests preconditions, not a cryptographic stretching candidate. -/
namespace Foundation.Examples.TypedSeedPrecondition
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
open Foundation.Symmetric.EncryptThenMAC
set_option backward.isDefEq.respectTransparency false

def generator : Generator where
  seedLength := id
  outputLength := id
  generate := fun _ => id

def code : Machine.Program := [.branch .output 1 0 0, .halt]

def finish (machine : Configuration) : Configuration :=
  {machine.resumeAt 1 with halted := true}

noncomputable def execution (width : Nat) :
    TimedExecution.Procedure (stepPMF code) (Bits width) Configuration :=
  (Machine.Procedure.ofFixed code
    (fun seed => (SeededGeneratorImplementation.seedEntry generator width seed).resumeAt 0)
    (fun _ result => result)
    (fun seed => PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator width seed)))
    (fun _ => 2)
    (fun seed => by
      have hb : (SeededGeneratorImplementation.seedEntry generator width seed).outputTape.current = none := rfl
      simp [evalConfigWithin, code, stepPMF, Machine.next, Configuration.resumeAt,
        Instruction.next, Configuration.tape, finish, hb, PMF.pure_map])).execution

noncomputable def expander : SeededGeneratorImplementation.Expander generator where
  Output := fun _ => Configuration
  code := code
  execution := execution
  closed := Program.controlClosed_step (by decide)
  entry := fun _ _ => rfl
  nonempty := by decide
  halted := fun width seed result h => by
    change result ∈ (PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator width seed))).support at h
    rw [PMF.mem_support_pure_iff] at h
    subst result
    rfl
  cap := fun _ => 2
  bounded := fun _ _ => Nat.le_refl _
  tape := fun width seed result h => by
    change result ∈ (PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator width seed))).support at h
    rw [PMF.mem_support_pure_iff] at h
    subst result
    rfl

theorem fixed_code : expander.projected.code = OneTimePad.keygen.followedBy code := rfl

theorem budget (width : Nat) : (expander.projected.execution width).budget () = 5 * width + 5 := by
  rw [SeededGeneratorImplementation.Expander.projected_budget]
  change 5 * width + 2 + 3 = _
  omega

/-- All widths, including zero, work from the actual sampler input. -/
theorem run (width horizon : Nat) (hTime : 5 * width + 5 ≤ horizon) :
    (evalConfigWithin (OneTimePad.keygen.followedBy code)
      (Configuration.initial (List.replicate width true)) horizon).map
        (SeededGeneratorImplementation.key generator width) = uniform (Bits width) := by
  change (evalConfigWithin (OneTimePad.keygen.followedBy expander.code)
    (Configuration.initial (List.replicate (generator.seedLength width) true)) horizon).map
      (SeededGeneratorImplementation.key generator width) = _
  rw [SeededGeneratorImplementation.Expander.assembled_run expander width horizon
    (by change 5 * width + 2 + 3 ≤ horizon; omega)]
  exact (expander.implements width ()).trans (PMF.map_id _)

/-- This configuration violates the seed-entry layout: its current output
cell contains data rather than the terminating blank. -/
def malformed : Configuration := { outputTape := Tape.ofBits [false] }

theorem malformed_self_loop : stepPMF code malformed = PMF.pure malformed := by
  simp [stepPMF, Machine.next, code, malformed, Instruction.next,
    Configuration.tape, Tape.ofBits]

theorem malformed_run (horizon : Nat) : evalConfigWithin code malformed horizon = PMF.pure malformed := by
  induction horizon with
  | zero => rfl
  | succ horizon ih =>
      rw [evalConfigWithin, ih, PMF.pure_bind, malformed_self_loop]

theorem malformed_never_halts (horizon : Nat) (target : Configuration)
    (h : target ∈ (evalConfigWithin code malformed horizon).support) : target.halted = false := by
  rw [malformed_run, PMF.mem_support_pure_iff] at h
  subst target
  rfl

/-- No global halting contract can cover this malformed physical entry.
The typed seed contract is therefore strictly less demanding. -/
theorem no_global_stopping_contract {Output : Type u} (P : Machine.Procedure Configuration Output)
    (hCode : P.code = code) (hEntry : P.execution.entry malformed = malformed) :
    ¬ (∀ output ∈ (P.execution.semantics malformed).support,
      (P.execution.exit malformed output).halted = true) := by
  intro hHalt
  have h := P.final_run malformed hHalt (P.execution.budget malformed) (Nat.le_refl _)
  rw [hEntry] at h
  have hr := (congrArg (fun nativeCode => evalConfigWithin nativeCode malformed
    (P.execution.budget malformed)) hCode).trans (malformed_run (P.execution.budget malformed))
  have heq := hr.symm.trans h
  have hm : malformed ∈ ((P.execution.semantics malformed).map (P.execution.exit malformed)).support := by
    rw [← heq]
    simp
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨output, ho, he⟩ := hm
  have ht := hHalt output ho
  rw [he] at ht
  change false = true at ht
  cases ht

end Foundation.Examples.TypedSeedPrecondition
