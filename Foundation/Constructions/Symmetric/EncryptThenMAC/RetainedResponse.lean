import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyCallback

/-! Reuse the actual retained secret store. Its left blank is consumed by
native rewind and restored to the same single blank; it is never erased by
a host-side normalization, nor does it accumulate across queries. -/
namespace Foundation.Symmetric.EncryptThenMAC.RetainedResponse
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def copying (before remaining : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { inputTape := { ResponseHandoff.fromCells (remaining.map some ++ [none]) with
      left := before.reverse.map some ++ [none] },
    outputTape := { left := outputBefore } }

def rewinding (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 8, inputTape := ⟨left.map some ++ [none], current, right⟩, outputTape := output }

theorem copy_cell (bit : Bool) (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying before (bit :: remaining) outputBefore) 6 =
      PMF.pure (copying (before ++ [bit]) remaining (some bit :: outputBefore)) := by
  cases bit <;> cases remaining <;>
    simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, copying, ResponseHandoff.fromCells,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight, List.reverse_append]

theorem copy_loop (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying before remaining outputBefore) (6 * remaining.length + 1) =
      PMF.pure (rewinding (before ++ remaining).reverse none []
        { left := remaining.reverse.map some ++ outputBefore }) := by
  induction remaining generalizing before outputBefore with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, copying, ResponseHandoff.fromCells,
        rewinding, Instruction.next, Configuration.tape]
  | cons bit remaining ih =>
      rw [show 6 * (bit :: remaining).length + 1 = 6 + (6 * remaining.length + 1) by simp; omega,
        evalConfigWithin_add, copy_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_cell (bit : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin PrivateKeyCopy.code (rewinding (bit :: left) current right output) 2 =
      PMF.pure (rewinding left (some bit) (current :: right) output) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, rewinding, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft]

theorem rewind_loop (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin PrivateKeyCopy.code (rewinding left current right output) (2 * left.length + 4) =
      PMF.pure ({ pc := 11, inputTape := PrivateKeyCopy.restored (left.reverse.map some ++ current :: right), outputTape := output, halted := true } : Configuration) := by
  induction left generalizing current right with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, rewinding, PrivateKeyCopy.restored,
        Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
        Tape.moveLeft, Tape.moveRight]
  | cons bit left ih =>
      rw [show 2 * (bit :: left).length + 4 = 2 + (2 * left.length + 4) by simp; omega,
        evalConfigWithin_add, rewind_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Full native copy result with exactly the same retained physical layout. -/
theorem copy_run (key : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying [] key outputBefore) (8 * key.length + 5) =
      PMF.pure (PrivateKeyCopy.finish key outputBefore) := by
  rw [show 8 * key.length + 5 = (6 * key.length + 1) + (2 * key.reverse.length + 4) by simp; omega,
    evalConfigWithin_add, copy_loop, PMF.pure_bind]
  simpa [PrivateKeyCopy.finish] using rewind_loop key.reverse none []
    ({ left := key.reverse.map some ++ outputBefore } : Tape)

def initial {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : ResponseHandoff.Control :=
  .headerWriting (ResponseHandoff.retainedKey key) (ResponseHandoff.header ciphertext) {}

theorem header_copying {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    { inputTape := ResponseHandoff.retainedKey key,
      outputTape := { left := (ResponseHandoff.header ciphertext).reverse.map some } : Configuration } =
      copying [] (ResponseHandoff.keyBytes key) ((ResponseHandoff.header ciphertext).reverse.map some) := by
  simp [copying, ResponseHandoff.retainedKey, PrivateKeyCopy.restored, ResponseHandoff.fromCells]

theorem completed_response {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval (ResponseHandoff.budget width ciphertext) (initial key ciphertext)).map
      PrivacyMachine.responseOutput =
      PMF.pure (some (ResponseHandoff.retainedKey key, AuthenticateResponse.responseTape key ciphertext)) := by
  have hBudget : ResponseHandoff.budget width ciphertext =
      (2 * (ResponseHandoff.header ciphertext).length + 1) +
        ((8 * (ResponseHandoff.keyBytes key).length + 5) +
          ((ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14))) := by
    rw [ResponseHandoff.keyBytes_length]
    unfold ResponseHandoff.budget
    omega
  rw [hBudget, ResponseHandoff.eval_add]
  unfold initial
  rw [ResponseHandoff.header_eval, PMF.pure_bind]
  simp only [List.append_nil, header_copying]
  exact PrivacyMachine.completed_response_of_copy_run key ciphertext _ (copy_run _ _)

end Foundation.Symmetric.EncryptThenMAC.RetainedResponse
