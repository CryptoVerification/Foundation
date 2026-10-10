import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure
import Foundation.Crypto.Semantics.Machine.BitstringRewind

/-! A charged scan with arbitrary cells to the right and an arbitrary other
tape. Exact physical representations, including outer blanks, are retained.
The opposite-tape variant compiles different tape operands, not a tape swap. -/
namespace Machine.NativeBitstringRewind
open Foundation.Probability TimedExecution

structure Input where
  bits : List Bool
  current : Option Bool := none
  right : List (Option Bool) := []
  other : Tape

def initial (input : Input) : Configuration :=
  { inputTape := {left := input.bits.reverse.map some, current := input.current, right := input.right},
    outputTape := input.other }

def finish (input : Input) : Configuration :=
  { pc := 3,
    inputTape := ({right := input.bits.map some ++ input.current :: input.right} : Tape).moveRight,
    outputTape := input.other, halted := true }

theorem run (input : Input) :
    evalConfigWithin rewindBitstring (initial input) (2 * input.bits.length + 4) =
      PMF.pure (finish input) :=
  (rewindBitstring_runs_from input.bits input.current input.right input.other).evalConfigWithin_eq_pure_of_no_randomBit
    rewindBitstring_no_randomBit

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed rewindBitstring initial (fun _ output => output)
    (fun input => PMF.pure (finish input)) (fun input => 2 * input.bits.length + 4)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 4; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

noncomputable def outputComponent : NativeComponent Input Configuration := component.swapTapes

theorem output_code : outputComponent.procedure.code = rewindBitstring.swapTapes := rfl

theorem output_budget (input : Input) :
    outputComponent.procedure.execution.budget input = 2 * input.bits.length + 4 := rfl

theorem output_run (input : Input) :
    evalConfigWithin outputComponent.procedure.code (initial input).swapTapes
      (2 * input.bits.length + 4) = PMF.pure (finish input).swapTapes := by
  rw [output_code, evalConfigWithin_swapTapes, run, PMF.pure_map]

theorem output_saved_input (input : Input) : (finish input).swapTapes.inputTape = input.other := rfl

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound rewindBitstring 0 (size + 1) (2 * size + 4)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
    (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))

theorem initial_cells (input : Input) :
    (initial input).tapeCells = input.bits.length + input.right.length + input.other.cells + 1 := by
  simp [initial, Configuration.tapeCells, Tape.cells]
  omega

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 2 * input.bits.length + 4) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF rewindBitstring) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (rewindBitstring, target)).length ≤
      bitBound (input.bits.length + input.right.length + input.other.cells) := by
  have h := NativeEncodedResources.peak rewindBitstring _ elapsed hElapsed _ target hTarget
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0)
    (by rw [initial_cells]) (by omega))

end Machine.NativeBitstringRewind

/-! The same four instructions with a physically represented separator.
Unlike outer-blank equivalence, this contract retains arbitrary saved cells
beyond the separator exactly. The trace is the existing scratch rewind. -/
namespace Machine.NativeBitstringRewind.Scratch
open Foundation.Probability TimedExecution

structure Input extends NativeBitstringRewind.Input where
  saved : List (Option Bool)

def initial (input : Input) : Configuration :=
  { inputTape := {left := input.bits.reverse.map some ++ none :: input.saved, current := input.current, right := input.right}, outputTape := input.other }

def finish (input : Input) : Configuration :=
  { pc := 3, inputTape := ({left := input.saved, right := input.bits.map some ++ input.current :: input.right} : Tape).moveRight,
    outputTape := input.other, halted := true }

theorem trace (input : Input) :
    RunsFor rewindBitstring (initial input) (finish input) (2 * input.bits.length + 4) :=
  rewindScratch_runs_from input.saved input.bits input.current input.right input.other

theorem run (input : Input) :
    evalConfigWithin rewindBitstring (initial input) (2 * input.bits.length + 4) =
      PMF.pure (finish input) :=
  (trace input).evalConfigWithin_eq_pure_of_no_randomBit rewindBitstring_no_randomBit

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed rewindBitstring initial (fun _ output => output)
    (fun input => PMF.pure (finish input)) (fun input => 2 * input.bits.length + 4)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 4; decide) (fun _ => rfl)
    (by intro input output h
        rw [PMF.mem_support_pure_iff] at h
        subst output
        rfl)

theorem code_eq : component.procedure.code = NativeBitstringRewind.component.procedure.code := rfl

/-- Saved cells contribute to storage, but do not lengthen the scan. -/
theorem initial_cells (input : Input) :
    (initial input).tapeCells = input.bits.length + input.saved.length +
      input.right.length + input.other.cells + 2 := by
  simp [initial, Configuration.tapeCells, Tape.cells]
  omega

theorem storage_peak (input : Input) (elapsed : Nat)
    (within : elapsed ≤ 2 * input.bits.length + 4) (target : Configuration)
    (support : target ∈ (TimedExecution.eval (stepPMF rewindBitstring) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (rewindBitstring, target)).length ≤
      NativeBitstringRewind.bitBound
        (input.bits.length + input.saved.length + input.right.length + input.other.cells + 1) := by
  have h := NativeEncodedResources.peak rewindBitstring _ elapsed within _ target support
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0)
    (by rw [initial_cells]) (by omega))

end Machine.NativeBitstringRewind.Scratch
