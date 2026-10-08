import Foundation.Crypto.Semantics.Machine.PairPreparation
import Foundation.Crypto.Semantics.Framing
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrimitiveContracts

/-! Prepare arbitrary-width pad operands from separate physical tapes.
Trailing cells and saved callers are retained. The exact produced buffer
executes the existing XOR program; no free blank normalization is used. -/
namespace Foundation.PairPreparationExamples
open Foundation.Probability TimedExecution
open Foundation.Symmetric Machine.PairPreparation
set_option backward.isDefEq.respectTransparency false

theorem interleave_eq (first second : List Bool) :
    interleave first second = Machine.OneTimePad.pairInput first second := by
  induction first generalizing second with
  | nil => rfl
  | cons bit first ih => cases second with
    | nil => rfl
    | cons next second => simp only [interleave, Machine.OneTimePad.pairInput, ih]

theorem prepare (width : Nat) (key message : Bits width)
    (keyTail messageTail : List (Option Bool)) :
    eval step (12 * width + 3)
      (.reading (operand [] key.toList keyTail) (operand [] message.toList messageTail) {}) =
      PMF.pure (.ready (operand [] key.toList keyTail) (operand [] message.toList messageTail)
        (fromCells ((Machine.OneTimePad.pairInput key.toList message.toList).map some ++ [none]))) := by
  simpa only [Bits.length_toList, interleave_eq] using
    Machine.PairPreparation.run key.toList message.toList keyTail messageTail (by simp)

theorem prepare_saved (width : Nat) (key message : Bits width)
    (keyTail messageTail : List (Option Bool)) (caller : Machine.Configuration) :
    eval (framedStep step) (12 * width + 3)
      (.reading (operand [] key.toList keyTail) (operand [] message.toList messageTail) {}, caller) =
      PMF.pure (.ready (operand [] key.toList keyTail) (operand [] message.toList messageTail)
        (fromCells ((Machine.OneTimePad.pairInput key.toList message.toList).map some ++ [none])), caller) := by
  rw [framed_eval, prepare, PMF.pure_map]

def preparedInput (width : Nat) (key message : Bits width) : Machine.Configuration :=
  { inputTape := fromCells ((Machine.OneTimePad.pairInput key.toList message.toList).map some ++ [none]) }

theorem prepared_layout (width : Nat) (key message : Bits width) :
    (preparedInput width key message).Equivalent
      (Machine.OneTimePad.state [] [] (Machine.OneTimePad.pairInput key.toList message.toList)) := by
  rw [Machine.OneTimePad.state_initial]
  exact ⟨rfl, rfl, prepared_equivalent _, Machine.Tape.Equivalent.refl _⟩

/-- Executes on the actual padded tape produced by preparation. The
observation includes native halt and is not an assertion from time expiry. -/
theorem prepared_xor (width : Nat) (key message : Bits width) :
    (Machine.evalConfigWithin Machine.OneTimePad.xorCode (preparedInput width key message) (8 * width + 2)).map
      (fun machine => (machine.halted, machine.outputBits)) =
      PMF.pure (true, (OneTimePad.encrypt key message).toList) := by
  rw [Machine.evalConfigWithin_map_eq_of_equivalent Machine.OneTimePad.xorCode _ _
    (prepared_layout width key message) (8 * width + 2) (fun machine => (machine.halted, machine.outputBits))
    (fun _ _ h => by rw [h.2.1, h.outputBits])]
  have h := Machine.OneTimePad.xor_run [] [] key.toList message.toList (by simp)
  rw [Bits.length_toList] at h
  rw [h, PMF.pure_map, Machine.OneTimePad.finish_output]
  simp [Machine.OneTimePad.finish, OneTimePad.encrypt, Machine.OneTimePad.toList_xor]

end Foundation.PairPreparationExamples
