import Foundation.Crypto.Semantics.Machine.PairPreparation
import Foundation.Crypto.Semantics.Machine.ResponsePacket

/-! Restore physical operands after rejected preparation, then write a tagged
failure response. No saved key is reconstructed from a semantic value. -/
namespace Machine.PreparationFailure
open Foundation.Probability TimedExecution

inductive Control where
  | detected (first second buffer : Tape)
  | restoring (preparation : PairPreparation.Control)
  | writing (first second : Tape) (packet : ResponsePacket.Control)
  | returned (first second response : Tape)
  deriving DecidableEq

noncomputable def step : Control → PMF Control
  | .detected first second buffer =>
      PMF.pure (.restoring (.rewinding first second buffer))
  | .restoring (.ready first second _) =>
      PMF.pure (.writing first second (.start none))
  | .restoring preparation => (PairPreparation.step preparation).map .restoring
  | .writing first second (.returned tape) => PMF.pure (.returned first second tape)
  | .writing first second packet => (ResponsePacket.step packet).map (.writing first second)
  | .returned first second response => PMF.pure (.returned first second response)

theorem restore (firstLeft secondLeft bufferLeft : List (Option Bool))
    (firstCurrent secondCurrent bufferCurrent : Option Bool)
    (firstRight secondRight bufferRight : List (Option Bool)) :
    eval step (firstLeft.length + secondLeft.length + bufferLeft.length + 2)
      (.restoring (.rewinding ⟨firstLeft, firstCurrent, firstRight⟩
        ⟨secondLeft, secondCurrent, secondRight⟩ ⟨bufferLeft, bufferCurrent, bufferRight⟩)) =
      PMF.pure (.writing (PairPreparation.fromCells (firstLeft.reverse ++ firstCurrent :: firstRight))
        (PairPreparation.fromCells (secondLeft.reverse ++ secondCurrent :: secondRight)) (.start none)) := by
  induction firstLeft generalizing firstCurrent firstRight with
  | cons cell firstLeft ih =>
      rw [show (cell :: firstLeft).length + secondLeft.length + bufferLeft.length + 2 =
        (firstLeft.length + secondLeft.length + bufferLeft.length + 2) + 1 by simp; omega, eval]
      simp only [step, PairPreparation.step, Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]
  | nil =>
      induction secondLeft generalizing secondCurrent secondRight with
      | cons cell secondLeft ih =>
          rw [show ([] : List (Option Bool)).length + (cell :: secondLeft).length + bufferLeft.length + 2 =
            (([] : List (Option Bool)).length + secondLeft.length + bufferLeft.length + 2) + 1 by simp; omega, eval]
          simp only [step, PairPreparation.step, Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
          rw [ih]
          simp [List.reverse_cons, List.append_assoc]
      | nil =>
          induction bufferLeft generalizing bufferCurrent bufferRight with
          | cons cell bufferLeft ih =>
              rw [show ([] : List (Option Bool)).length + ([] : List (Option Bool)).length +
                (cell :: bufferLeft).length + 2 =
                (([] : List (Option Bool)).length + ([] : List (Option Bool)).length + bufferLeft.length + 2) + 1 by simp,
                eval]
              simp only [step, PairPreparation.step, Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
              rw [ih]
          | nil => simp [eval, step, PairPreparation.step, PairPreparation.fromCells]

theorem write_failure (first second : Tape) :
    eval step 4 (.writing first second (.start none)) =
      PMF.pure (.returned first second (ResponseExport.endTape [false])) := by
  simp [eval, step, ResponsePacket.step, Tape.write, Tape.moveRight, ResponseExport.endTape]

def restored (tape : Tape) : Tape :=
  PairPreparation.fromCells (tape.left.reverse ++ tape.current :: tape.right)

theorem run (first second buffer : Tape) :
    eval step (first.left.length + second.left.length + buffer.left.length + 7)
      (.detected first second buffer) =
      PMF.pure (.returned (restored first) (restored second) (ResponseExport.endTape [false])) := by
  rw [show first.left.length + second.left.length + buffer.left.length + 7 =
    ((first.left.length + second.left.length + buffer.left.length + 2) + 4) + 1 by omega,
    eval]
  simp only [step, PMF.pure_bind]
  rw [eval_add step (first.left.length + second.left.length + buffer.left.length + 2) 4,
    restore, PMF.pure_bind, write_failure]
  rfl

noncomputable def procedure : TimedExecution.Procedure step (Tape × Tape × Tape) Unit :=
  TimedExecution.Procedure.ofFixed step
    (fun input => .detected input.1 input.2.1 input.2.2)
    (fun input _ => .returned (restored input.1) (restored input.2.1) (ResponseExport.endTape [false]))
    (fun _ => PMF.pure ())
    (fun input => input.1.left.length + input.2.1.left.length + input.2.2.left.length + 7)
    (fun input => by simpa only [PMF.pure_map] using run input.1 input.2.1 input.2.2)

end Machine.PreparationFailure
