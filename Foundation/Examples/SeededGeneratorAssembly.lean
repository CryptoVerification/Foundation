import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorSecurity
import Foundation.Crypto.Semantics.Machine.TypedCompositionRelation

/-! Arbitrary-width regression for the native seeded assembly interface.
The expander is identity: this validates the actual finite linking, retained
input tape and projected result contract, not a stretching PRG candidate. -/
namespace Foundation.Examples.SeededGeneratorAssembly
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
open Foundation.Symmetric.EncryptThenMAC
set_option backward.isDefEq.respectTransparency false

def generator : Generator where
  seedLength := id
  outputLength := id
  generate := fun _ => id

def finish (machine : Configuration) : Configuration :=
  {machine.resumeAt 0 with halted := true}

noncomputable def stop : Machine.Procedure Configuration Configuration :=
  Machine.Procedure.ofFixed [.halt] (fun machine => machine.resumeAt 0)
    (fun _ result => result) (fun machine => PMF.pure (finish machine)) (fun _ => 1)
    (fun machine => by
      simp [evalConfigWithin, stepPMF, Machine.next, Configuration.resumeAt, Instruction.next,
        finish, PMF.pure_map])

noncomputable def expander : SeededGeneratorImplementation.Expander generator where
  Output := fun _ => Configuration
  code := [.halt]
  execution := fun n => stop.execution.reindex (SeededGeneratorImplementation.seedEntry generator n)
  closed := Program.controlClosed_step (by decide)
  entry := fun _ _ => rfl
  nonempty := by decide
  halted := fun n seed output h => by
    change output ∈ (PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator n seed))).support at h
    rw [PMF.mem_support_pure_iff] at h
    subst output
    rfl
  cap := fun _ => 1
  bounded := fun _ _ => Nat.le_refl _
  tape := fun n seed output h => by
    change output ∈ (PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator n seed))).support at h
    rw [PMF.mem_support_pure_iff] at h
    subst output
    rfl

theorem fixed_code : expander.projected.code = OneTimePad.keygen.followedBy [.halt] := rfl

theorem code_length : expander.projected.code.length = 10 := by decide

theorem budget (width : Nat) : (expander.projected.execution width).budget () = 5 * width + 4 := by
  rw [SeededGeneratorImplementation.Expander.projected_budget]
  change 5 * width + 1 + 3 = _
  omega

theorem key_distribution (width : Nat) :
    ((expander.projected.execution width).semantics ()).map (expander.projected.key width) =
      uniform (Bits width) := by
  rw [expander.projected.implements]
  exact PMF.map_id _

/-- The actual linked finite code, observed at any sufficient horizon. -/
theorem run (width horizon : Nat) (hTime : 5 * width + 4 ≤ horizon) :
    (evalConfigWithin expander.projected.code
      (Configuration.initial (List.replicate width true)) horizon).map
        (SeededGeneratorImplementation.key generator width) = uniform (Bits width) := by
  change (evalConfigWithin (OneTimePad.keygen.followedBy expander.code)
    (Configuration.initial (List.replicate (generator.seedLength width) true)) horizon).map
      (SeededGeneratorImplementation.key generator width) = uniform (Bits width)
  rw [SeededGeneratorImplementation.Expander.assembled_run expander width horizon
    (by change 5 * width + 1 + 3 ≤ horizon; omega)]
  exact (expander.implements width ()).trans (PMF.map_id _)

/-- The internal result still contains the consumed marker input tape. -/
theorem input_retained (width : Nat) (machine : Configuration)
    (h : machine ∈ ((expander.assembled width).execution.semantics ()).support) :
    machine.inputTape = ResponseExport.endTape (List.replicate width true) := by
  apply (expander.link width).inputTape_frame
    (fun _ => ResponseExport.endTape (List.replicate width true)) _ _ () machine h
  · intro input seed _
    rfl
  · intro seed output ho
    change output ∈ (PMF.pure (finish
      (SeededGeneratorImplementation.seedEntry generator width seed))).support at ho
    rw [PMF.mem_support_pure_iff] at ho
    subst output
    rfl

theorem time_polynomial : PolynomiallyBounded (fun width => (expander.projected.execution width).budget ()) :=
  expander.time_polynomial PolynomiallyBounded.id (PolynomiallyBounded.const 1)

end Foundation.Examples.SeededGeneratorAssembly
