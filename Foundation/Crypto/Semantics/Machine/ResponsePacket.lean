import Foundation.Crypto.Semantics.Encoding
import Foundation.Crypto.Semantics.Machine.ResponseExport

/-! Charged physical writing of tagged success/failure packets. This finite
controller writes each cell and moves the head in separate transitions.
It is a controller contract, not a compilation into a native instruction list. -/
namespace Machine.ResponsePacket
open Foundation.Probability TimedExecution

def codec := (Foundation.Encoding.identity (List Bool)).optionBits

inductive Control where
  | start (response : Option (List Bool))
  | writing (remaining : List Bool) (tape : Tape)
  | advancing (remaining : List Bool) (tape : Tape)
  | returned (tape : Tape)
  deriving DecidableEq

noncomputable def step : Control → PMF Control
  | .start none => PMF.pure (.advancing [] (({} : Tape).write (some false)))
  | .start (some payload) =>
      PMF.pure (.advancing payload (({} : Tape).write (some true)))
  | .writing [] tape => PMF.pure (.returned tape)
  | .writing (bit :: rest) tape => PMF.pure (.advancing rest (tape.write (some bit)))
  | .advancing remaining tape => PMF.pure (.writing remaining tape.moveRight)
  | .returned tape => PMF.pure (.returned tape)

theorem write_run (remaining before : List Bool) :
    eval step (2 * remaining.length + 1)
      (.writing remaining (ResponseExport.endTape before)) =
      PMF.pure (.returned (ResponseExport.endTape (before ++ remaining))) := by
  induction remaining generalizing before with
  | nil => simp [eval, step]
  | cons bit rest ih =>
      rw [show 2 * (bit :: rest).length + 1 = (2 * rest.length + 1) + 1 + 1 by simp; omega]
      rw [eval]
      simp only [step, PMF.pure_bind]
      rw [eval]
      simp only [step, PMF.pure_bind]
      have ht : ((ResponseExport.endTape before).write (some bit)).moveRight =
          ResponseExport.endTape (before ++ [bit]) := by
        simp [ResponseExport.endTape, Tape.write, Tape.moveRight, List.reverse_append]
      rw [ht, ih]
      simp [List.append_assoc]

def budget (response : Option (List Bool)) : Nat :=
  2 * (response.getD []).length + 3

theorem run (response : Option (List Bool)) :
    eval step (budget response) (.start response) =
      PMF.pure (.returned (ResponseExport.endTape (codec.encode response))) := by
  cases response with
  | none => simp [budget, eval, step, codec, Foundation.Encoding.optionBits, ResponseExport.endTape, Tape.write, Tape.moveRight]
  | some payload =>
      rw [show budget (some payload) = (2 * payload.length + 1) + 1 + 1 by simp [budget]]
      rw [eval]
      simp only [step, PMF.pure_bind]
      rw [eval]
      simp only [step, PMF.pure_bind]
      simpa [ResponseExport.endTape, Tape.write, Tape.moveRight, codec,
        Foundation.Encoding.optionBits, Foundation.Encoding.identity] using write_run payload [true]

noncomputable def procedure : TimedExecution.Procedure step (Option (List Bool)) Unit :=
  TimedExecution.Procedure.ofFixed step Control.start
    (fun response _ => .returned (ResponseExport.endTape (codec.encode response)))
    (fun _ => PMF.pure ()) budget
    (fun response => by simpa only [PMF.pure_map] using run response)

/-- Empty success is a one-bit packet and is distinct from failure. -/
theorem empty_success_ne_failure : codec.encode (some []) ≠ codec.encode none := by
  decide

theorem written_bits (response : Option (List Bool)) :
    (ResponseExport.endTape (codec.encode response)).bits = codec.encode response := by
  simp [ResponseExport.endTape, Tape.bits, List.map_reverse]

/-- Both layers of Option matter: malformed packets versus valid rejection. -/
theorem written_decode (response : Option (List Bool)) :
    codec.decode (ResponseExport.endTape (codec.encode response)).bits = some response := by
  rw [written_bits, codec.roundtrip]

theorem final_cells (response : Option (List Bool)) :
    (ResponseExport.endTape (codec.encode response)).cells = (response.getD []).length + 2 := by
  cases response <;> simp [ResponseExport.endTape, Tape.cells, codec,
    Foundation.Encoding.optionBits, Foundation.Encoding.identity, Nat.add_comm] <;> omega

/-- Retaining a private store is an entry condition; no copy is hidden here. -/
theorem saved_run {Saved : Type*} (response : Option (List Bool)) (saved : Saved) :
    eval (framedStep step) (budget response) (.start response, saved) =
      PMF.pure (.returned (ResponseExport.endTape (codec.encode response)), saved) := by
  rw [framed_eval, run, PMF.pure_map]

end Machine.ResponsePacket
