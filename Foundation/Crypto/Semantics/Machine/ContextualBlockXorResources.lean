import Foundation.Crypto.Semantics.Machine.ContextualBlockXor

/-! Space and time bounds for contextual masking include all saved context.
Large padding or unrelated stored data cannot be omitted from the physical
input size. The bound uses the unchanged code's complete state encoding. -/
namespace Machine.FlaggedBlockXor.Contextual
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- All context cells count toward the input size parameter. -/
def inputSize (input : Input) : Nat :=
  input.message.length + input.inputFrame.length + input.inputSuffix.length + input.outputSuffix.length

theorem initial_cells (input : Input) :
    (initial input).tapeCells = 4 * input.message.length + 4 +
      input.inputFrame.length + input.inputSuffix.length + input.outputSuffix.length := by
  have hLength : (request input.message ++ input.key).length = 3 * input.message.length + 1 := by
    simp only [List.length_append, request_length, input.sameLength]
    omega
  rw [initial_eq]
  cases hPacket : request input.message ++ input.key with
  | nil => simp only [hPacket, List.length_nil] at hLength; omega
  | cons bit rest =>
      simp only [hPacket, List.length_cons] at hLength
      simp [Configuration.tapeCells, Tape.cells, OneTimePad.delimitedTape]
      omega

theorem initial_cells_bound (input : Input) : (initial input).tapeCells ≤ 4 * inputSize input + 4 := by
  rw [initial_cells]
  unfold inputSize
  omega

theorem budget (input : Input) : component.procedure.execution.budget input = 24 * input.message.length + 8 := rfl

theorem budget_bound (input : Input) : component.procedure.execution.budget input ≤ 24 * inputSize input + 8 := by
  rw [budget]
  unfold inputSize
  omega

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound code 0 (4 * size + 4) (24 * size + 8)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))
    (((PolynomiallyBounded.const 24).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 8))

/-- The complete encoding of every intermediate state is bounded. -/
theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 24 * input.message.length + 8)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF code) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (code, target)).length ≤ bitBound (inputSize input) :=
  (NativeEncodedResources.peak code _ elapsed hElapsed _ target hTarget).trans
    (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) (initial_cells_bound input) (by unfold inputSize; omega))

end Machine.FlaggedBlockXor.Contextual
