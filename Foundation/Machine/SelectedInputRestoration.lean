import Foundation.Machine.SelectedMessagePreparation
import Foundation.Machine.StoredInputRewind

namespace Machine

/-- A copied selected message leaves the original canonical response split
at a known prefix. The older raw reply and DDH input are still behind their
physical blanks. This identifies the existing cells for the native rewind;
it supplies no fresh DDH input and does not change either tape. -/
theorem prepareSelectedMessageFinish_restore_layout (before beforeOutput : List (Option Bool))
    (original reply first second state : List Bool) (blanks : Nat) (bit : Bool) :
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
    returned.resumeAt 0 = restoreStoredInputStart before original reply
      (selectedMessageConsumed first second bit) returned.inputTape.current
      returned.inputTape.right returned.outputTape := by
  dsimp only
  let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
  have hLeft : returned.inputTape.left =
      (selectedMessageConsumed first second bit).reverse.map some ++ none :: reply.reverse.map some ++
        none :: original.reverse.map some ++ none :: before := by
    dsimp only [returned]
    rw [prepareSelectedMessageFinish_input]
    simp [saved, List.append_assoc]
  have hTape : returned.inputTape = { returned.inputTape with
      left := (selectedMessageConsumed first second bit).reverse.map some ++ none :: reply.reverse.map some ++
        none :: original.reverse.map some ++ none :: before } := by
    rw [← hLeft]
  exact congrArg (fun tape => ({ inputTape := tape, outputTape := returned.outputTape } : Configuration)) hTape

/-- Native DDH restoration from the actual selected-message return. The
copied raw element code and sampled challenge bit on the other tape remain
unchanged, and all three input blocks remain stored for later request assembly. -/
theorem selectedMessage_restore_eval (before beforeOutput : List (Option Bool))
    (original reply first second state : List Bool) (blanks : Nat) (bit : Bool) :
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
    evalConfigWithin restoreStoredInput (returned.resumeAt 0)
      (restoreStoredInputSteps original reply (selectedMessageConsumed first second bit)) =
      PMF.pure (restoreStoredInputFinish before original reply (selectedMessageConsumed first second bit)
        returned.inputTape.current returned.inputTape.right returned.outputTape) := by
  dsimp only
  rw [prepareSelectedMessageFinish_restore_layout]
  exact restoreStoredInput_eval _ _ _ _ _ _ _

end Machine
