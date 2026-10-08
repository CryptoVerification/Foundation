import Foundation.Crypto.Semantics.Machine.ProgramRanking
import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Machine.PolynomialTime
import Foundation.Crypto.Semantics.Machine.NativeEncodedResources

/-! A reusable arbitrary-width native sampler with stopping proved from local
phase assertions and a remaining-work rank. The proof does not assume its
previous whole-program stopping theorem. That theorem is reused separately
only to identify the resulting key distribution. -/
namespace Machine.PrivateBitGeneration.Ranked
open Machine Foundation.Probability TimedExecution Foundation.Symmetric

/-- A bound for unconsumed input cells; represented blank gaps are counted. -/
def remaining (input : Tape) : Nat := input.right.length + if input.current.isSome then 1 else 0

theorem remaining_positive (input : Tape) (h : input.current.isSome = true) : 0 < remaining input := by
  simp [remaining, h]

theorem remaining_moveRight (input : Tape) (h : input.current.isSome = true) :
    remaining input.moveRight + 1 ≤ remaining input := by
  rcases input with ⟨left, current, right⟩
  cases right with
  | nil => simp_all [remaining, Tape.moveRight]
  | cons head rest =>
      cases head <;> simp_all [remaining, Tape.moveRight]

def assertions : Machine.Program.Assertions where
  active pc input _ := pc = 0 ∨ ((pc = 1 ∨ pc = 2) ∧ input.current.isSome = true) ∨
    pc = 3 ∨ pc = 4 ∨ pc = 5
  stopped _ _ _ := True

theorem verified : assertions.Verified Machine.OneTimePad.keygen := by
  constructor
  · intro pc start hPc hActive hAssertion
    fin_cases pc
    all_goals
      cases hCurrent : start.inputTape.current with
      | none =>
          simp_all [Machine.OneTimePad.keygen, assertions, Program.Assertions.Holds, Instruction.precondition,
            Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]
      | some bit =>
          cases bit <;>
            simp_all [Machine.OneTimePad.keygen, assertions, Program.Assertions.Holds, Instruction.precondition,
              Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]
  · intro pc input output _ _
    trivial

/-- Phase offsets count every branch, random write, head move, jump and halt. -/
def rank (machine : Configuration) : Nat :=
  match machine.pc with
  | 0 => 5 * remaining machine.inputTape + 1
  | 1 => 5 * remaining machine.inputTape
  | 2 => 5 * remaining machine.inputTape - 1
  | 3 => 5 * remaining machine.inputTape + 3
  | 4 => 5 * remaining machine.inputTape + 2
  | _ => 0

def ranking : Program.Ranking assertions Machine.OneTimePad.keygen where
  rank := rank
  instruction := by
    intro pc start hPc hActive hAssertion
    have hMove := remaining_moveRight start.inputTape
    have hPositive := remaining_positive start.inputTape
    fin_cases pc
    all_goals
      cases hCurrent : start.inputTape.current with
      | none =>
          simp_all [Machine.OneTimePad.keygen, assertions, Program.Assertions.Holds, Instruction.precondition,
            Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape, rank]
      | some bit =>
          cases bit <;>
            simp_all [Machine.OneTimePad.keygen, assertions, Program.Assertions.Holds, Instruction.precondition,
              Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape, rank] <;> omega

theorem initial_valid (bits : List Bool) : assertions.Holds (Configuration.initial bits) := by
  simp [assertions, Program.Assertions.Holds, Configuration.initial]

/-- The code is fixed; width only determines the actual marker input. -/
noncomputable def native : Machine.Procedure Nat
    {state // assertions.Holds state ∧ state.halted = true} :=
  ranking.onInputs verified (fun width => Configuration.initial (List.replicate width true))
    (fun _ => initial_valid _)

theorem remaining_initial (bits : List Bool) : remaining (Tape.ofBits bits) = bits.length := by
  cases bits <;> simp [remaining, Tape.ofBits]

theorem budget (width : Nat) : native.execution.budget width = 5 * width + 2 := by
  change rank (Configuration.initial (List.replicate width true)) + 1 = _
  simp [rank, Configuration.initial, remaining_initial]

theorem fixed_code : native.code = Machine.OneTimePad.keygen := rfl

theorem time_polynomial : PolynomiallyBounded native.execution.budget := by
  have he : native.execution.budget = fun width => 5 * width + 2 := by
    funext width
    exact budget width
  rw [he]
  exact ((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2)

/-- Stopping and the whole runtime equality come from the ranking rules. -/
theorem run (width horizon : Nat) (hTime : 5 * width + 2 ≤ horizon) :
    evalConfigWithin Machine.OneTimePad.keygen (Configuration.initial (List.replicate width true)) horizon =
      (native.execution.semantics width).map Subtype.val := by
  apply ranking.run verified _ _ width horizon
  change rank (Configuration.initial (List.replicate width true)) + 1 ≤ horizon
  change native.execution.budget width ≤ horizon
  rw [budget]
  exact hTime

/-- The original functional sampler proof identifies the entire physical
endpoint distribution, independently of the new derivation of stopping. -/
theorem physical_distribution (width : Nat) :
    (native.execution.semantics width).map Subtype.val =
      ((PrivateBitGeneration.native width).execution.semantics ()).map
        ((PrivateBitGeneration.native width).execution.exit ()) := by
  exact (run width (5 * width + 2) (Nat.le_refl _)).symm.trans
    ((PrivateBitGeneration.native width).final_run ()
      (fun key _ => PrivateBitGeneration.halted width () key) (5 * width + 2) (Nat.le_refl _))

/-- Distributional identification reuses the existing sampler's functional
proof, while the new stopping certificate is obtained independently above. -/
theorem key_distribution (width : Nat) :
    (native.execution.semantics width).map
      (fun result => PrivateBitGeneration.read width () result.val) = uniform (Bits width) := by
  have hRun := run width (5 * width + 2) (Nat.le_refl _)
  have hOld := (PrivateBitGeneration.native width).final_run () (fun key _ => PrivateBitGeneration.halted width () key)
    (5 * width + 2) (Nat.le_refl _)
  have h := congrArg (fun distribution => distribution.map (PrivateBitGeneration.read width ()))
    (hRun.symm.trans hOld)
  simp only [PMF.map_comp, Function.comp_def, PrivateBitGeneration.read_exit] at h
  change (native.execution.semantics width).map
    (fun result => PrivateBitGeneration.read width () result.val) = (uniform (Bits width)).map id at h
  rw [PMF.map_id] at h
  exact h

/-- Reading a supported physical result reconstructs the same full endpoint.
No equality is assumed for malformed or unsupported physical configurations. -/
private theorem recover (width : Nat)
    (result : {state // assertions.Holds state ∧ state.halted = true})
    (h : result ∈ (native.execution.semantics width).support) :
    (PrivateBitGeneration.native width).execution.exit ()
      (PrivateBitGeneration.read width () result.val) = result.val := by
  have hPhysical : result.val ∈ ((native.execution.semantics width).map Subtype.val).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, h, rfl⟩
  rw [physical_distribution, PMF.mem_support_map_iff] at hPhysical
  obtain ⟨key, _, he⟩ := hPhysical
  rw [← he, PrivateBitGeneration.read_exit]

/-- The usual typed seed interface, now retaining actual first-arrival costs
from the ranked execution. The finite code and physical entry are unchanged. -/
noncomputable def typed (width : Nat) : Machine.Procedure Unit (Bits width) :=
  ⟨Machine.OneTimePad.keygen,
    (native.execution.reindex (fun _ : Unit => width)).observe
      (fun result => PrivateBitGeneration.read width () result.val)
      (fun _ key => (PrivateBitGeneration.native width).execution.exit () key)
      (fun _ result h => recover width result h)⟩

theorem typed_code (width : Nat) : (typed width).code = Machine.OneTimePad.keygen := rfl

theorem typed_entry (width : Nat) (input : Unit) :
    (typed width).execution.entry input = (PrivateBitGeneration.native width).execution.entry input := rfl

theorem typed_exit (width : Nat) (input : Unit) (key : Bits width) :
    (typed width).execution.exit input key = (PrivateBitGeneration.native width).execution.exit input key := rfl

theorem typed_operational (width : Nat) : TimedExecution.Procedure.Operational (typed width).execution := by
  apply TimedExecution.Procedure.operational_observe
  apply TimedExecution.Procedure.operational_reindex
  exact ranking.operational verified
    (fun width => Configuration.initial (List.replicate width true)) (fun _ => initial_valid _)
  intro input output h
  exact recover width output h

theorem typed_budget (width : Nat) : (typed width).execution.budget () = 5 * width + 2 :=
  budget width

theorem typed_semantics (width : Nat) : (typed width).execution.semantics () = uniform (Bits width) :=
  key_distribution width

/-- Decoding the logical seed does not replace actual arrival time by a cap. -/
theorem typed_costed (width : Nat) :
    ((typed width).execution.costed ()).map (fun result =>
      ((PrivateBitGeneration.native width).execution.exit () result.1, result.2)) =
      runToBoundary (stepPMF Machine.OneTimePad.keygen) Configuration.halted (5 * width + 2)
        (Configuration.initial (List.replicate width true)) := by
  have hErase : ((typed width).execution.costed ()).map (fun result =>
      ((PrivateBitGeneration.native width).execution.exit () result.1, result.2)) =
      (native.execution.costed width).map (fun result => (result.1.val, result.2)) := by
    change ((native.execution.costed width).map _).map _ = _
    rw [PMF.map_comp, PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext result hs
    simp only [Function.comp_def, recover width result.1 (native.execution.result_support width result hs)]
  have h := ranking.costed verified
    (fun width => Configuration.initial (List.replicate width true)) (fun _ => initial_valid _) width
  change (native.execution.costed width).map (fun result => (result.1.val, result.2)) =
    runToBoundary (stepPMF Machine.OneTimePad.keygen) Configuration.halted
      (native.execution.budget width) (Configuration.initial (List.replicate width true)) at h
  rw [budget] at h
  exact hErase.trans h

/-- Full code and state storage, derived from the independently ranked time. -/
def bitBound (width : Nat) : Nat :=
  NativeEncodedResources.bound Machine.OneTimePad.keygen 0 (width + 2) (5 * width + 2)

theorem storage_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

theorem storage_peak (width elapsed : Nat) (hElapsed : elapsed ≤ 5 * width + 2)
    (target : Configuration)
    (hTarget : target ∈ (evalConfigWithin Machine.OneTimePad.keygen
      (Configuration.initial (List.replicate width true)) elapsed).support) :
    (NativeEncodedResources.completeEncoding.encode (Machine.OneTimePad.keygen, target)).length ≤ bitBound width := by
  have hCells : (Configuration.initial (List.replicate width true)).tapeCells ≤ width + 2 := by
    have h := Tape.cells_ofBits_le (List.replicate width true)
    simp only [List.length_replicate] at h
    change (Tape.ofBits (List.replicate width true)).cells + 1 ≤ width + 2
    omega
  have h := NativeEncodedResources.peak Machine.OneTimePad.keygen (5 * width + 2) elapsed hElapsed
    (Configuration.initial (List.replicate width true)) target (by rwa [timed_eval_eq])
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) hCells (Nat.le_refl _))

end Machine.PrivateBitGeneration.Ranked
