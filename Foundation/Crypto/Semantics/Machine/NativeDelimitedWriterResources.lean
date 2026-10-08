import Foundation.Crypto.Semantics.Machine.NativeDelimitedWriter

/-! Resource contracts of actual bitstring serialization count input data,
output capacity and every saved cell. Bounds use structural code encoding. -/
namespace Machine.NativeDelimitedWriter
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def inputSize (input : Input) : Nat :=
  input.data.length + input.inputFrame.length + input.outputFrame.length +
    input.inputSuffix.length + input.outputSuffix.length

theorem initial_cells (input : Input) : (initial input).tapeCells =
    3 * input.data.length + 3 + input.inputFrame.length + input.outputFrame.length +
      input.inputSuffix.length + input.outputSuffix.length := by
  rw [initial_eq]
  cases hData : input.data <;>
    simp [Configuration.tapeCells, Tape.cells, OneTimePad.delimitedTape]
  all_goals omega

theorem initial_cells_bound (input : Input) : (initial input).tapeCells ≤ 3 * inputSize input + 3 := by
  rw [initial_cells]
  unfold inputSize
  omega

theorem budget (input : Input) : component.procedure.execution.budget input = 8 * input.data.length + 4 := rfl

theorem budget_bound (input : Input) : component.procedure.execution.budget input ≤ 8 * inputSize input + 4 := by
  rw [budget]
  unfold inputSize
  omega

def bitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound NativeFlaggedRequest.code 0 (3 * size + 3) (8 * size + 4)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 8 * input.data.length + 4)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF NativeFlaggedRequest.code) elapsed (initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (NativeFlaggedRequest.code, state)).length ≤
      bitBound (inputSize input) :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells_bound input) (by unfold inputSize; omega))

/-- The encoded packet's exact logical size includes its final delimiter. -/
theorem packet_length (input : Input) : (FiniteBitEncoding.delimit input.data).length = 2 * input.data.length + 1 :=
  FiniteBitEncoding.delimit_length _

theorem firstArrival_fixed_time (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (component.firstArrival.procedure.execution.costed input).support) :
    result.2 = 8 * input.data.length + 4 := by
  rw [firstArrival_joint, PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Machine.NativeDelimitedWriter
