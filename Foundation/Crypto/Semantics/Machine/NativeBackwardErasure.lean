import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.BitstringErasure
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure

/-! The existing charged backward eraser as a reusable native component,
with arbitrary saved cells on both sides and an arbitrary other tape. -/
namespace Machine.NativeBackwardErasure
open Foundation.Probability TimedExecution

structure Input where
  bits : List Bool
  before : List (Option Bool) := []
  right : List (Option Bool) := []
  other : Tape

def initial (input : Input) : Configuration :=
  eraseOutputBlockStart input.other input.before input.bits input.right

def finish (input : Input) : Configuration :=
  eraseOutputBlockFinish input.other input.before input.bits input.right

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed eraseOutputBlock initial (fun _ output => output)
    (fun input => PMF.pure (finish input)) (fun input => 4 * input.bits.length + 3)
    (fun input => by simpa only [PMF.pure_map, initial, finish] using
      eraseOutputBlock_eval input.other input.before input.bits input.right)
    (by decide) (fun _ => by change 0 < 5; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

noncomputable def inputComponent : NativeComponent Input Configuration := component.swapTapes

theorem budget (input : Input) : component.procedure.execution.budget input = 4 * input.bits.length + 3 := rfl

theorem saved_other (input : Input) : (finish input).inputTape = input.other := rfl

theorem output_cells (input : Input) : (finish input).outputTape =
    {left := input.before, right := List.replicate (input.bits.length + 1) none ++ input.right} := by
  change ({left := input.before, right := List.replicate (input.bits.reverse.length + 1) none ++ input.right} : Tape) = _
  rw [List.length_reverse]

theorem output_blank (input : Input) (hBefore : input.before = []) (hRight : input.right = []) :
    (finish input).outputTape.Equivalent ({} : Tape) := by
  rw [output_cells, hBefore, hRight, List.append_nil]
  exact Tape.blank_padding_equivalent [] _

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound eraseOutputBlock 0 (size + 2) (4 * size + 3)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))

theorem initial_cells (input : Input) : (initial input).tapeCells =
    input.bits.length + input.before.length + input.right.length + input.other.cells + 2 := by
  change input.other.cells +
    ({left := input.bits.reverse.map some ++ none :: input.before, right := input.right} : Tape).cells = _
  simp only [Tape.cells, List.length_append, List.length_map, List.length_reverse, List.length_cons]
  omega

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 4 * input.bits.length + 3) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF eraseOutputBlock) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (eraseOutputBlock, target)).length ≤
      bitBound (input.bits.length + input.before.length + input.right.length + input.other.cells) := by
  have h := NativeEncodedResources.peak eraseOutputBlock _ elapsed hElapsed _ target hTarget
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0)
    (by rw [initial_cells]) (by omega))

end Machine.NativeBackwardErasure
