import Foundation.Crypto.Semantics.Oracle.PreparedCallback
import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! A source call enters a fixed native handler using its actual request
tape. Suspended source data is stored in runtime control. Returning a loaded
response transfers back to the source in one charged step. Call-use policy
and failure encoding are obligations of the surrounding construction. -/
namespace CryptoOracle.Interactive.SourceEntry
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | source (privateStore : Machine.Tape) (frame : Configuration State)
  | handling (machine : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool) (handler : PreparedCallback.Control State)

variable {State : Type u}

noncomputable def step (native : Machine.Program) (code : Code) (oracle : BitOracle State) :
    Control State → PMF (Control State)
  | .source key frame =>
      match frame.control with
      | .awaiting machine request => PMF.pure (.handling machine frame.state frame.reverseTrace request
          (.preparing (.reading key machine.outputTape {})))
      | _ => (Reification.timedStep code oracle frame).map (.source key)
  | .handling _ _ _ _ (.calling key _ (.source ⟨state, .running machine, trace⟩)) =>
      PMF.pure (.source key ⟨state, .running machine, trace⟩)
  | .handling machine state trace request handler =>
      (PreparedCallback.step native code oracle machine state trace request handler).map
        (.handling machine state trace request)

variable (native : Machine.Program) (code : Code) (oracle : BitOracle State)

theorem collect (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (bits reversed : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (bits.length + 1)
      (.source key ⟨state, .sending machine (RequestExport.packetTape before after bits) reversed, trace⟩) =
      PMF.pure (.source key ⟨state, .reversing machine (bits.reverse ++ reversed) [], trace⟩) := by
  induction bits generalizing reversed before with
  | nil =>
      simp [TimedExecution.eval, step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, PMF.pure_map]
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, List.map_cons,
        List.cons_append, List.headD_cons, List.tail_cons, Machine.Tape.moveRight, PMF.pure_map, PMF.pure_bind]
      cases bits <;> simpa [RequestExport.packetTape, List.reverse_cons, List.append_assoc]
        using ih (bit :: reversed) (some bit :: before)

theorem reverse (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (step native code oracle) (remaining.length + 1)
      (.source key ⟨state, .reversing machine remaining request, trace⟩) =
      PMF.pure (.source key ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩) := by
  induction remaining generalizing request with
  | nil =>
      simp [TimedExecution.eval, step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem export_run (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (2 * request.length + 2)
      (.source key ⟨state, .sending machine (RequestExport.packetTape before after request) [], trace⟩) =
      PMF.pure (.source key ⟨state, .awaiting machine request, trace⟩) := by
  rw [show 2 * request.length + 2 = (request.length + 1) + (request.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse]
  simp

/-- Capture, request export and transfer into physical input preparation. -/
theorem call_entry (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (step native code oracle) (2 * request.length + 4)
      (.source key ⟨state, .running machine, trace⟩) =
      PMF.pure (.handling machine.advance state trace request
        (.preparing (.reading key machine.outputTape {}))) := by
  rw [show 2 * request.length + 4 = ((2 * request.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [step, Reification.timedStep, Reification.terminal, hActive, Bool.false_eq_true, ↓reduceIte,
    Reification.perform, Reification.action, transition, hCall, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (step native code oracle) (2 * request.length + 2) 1]
  rw [hTape, export_run, PMF.pure_bind]
  simp [TimedExecution.eval, step, Machine.Configuration.advance, hTape]

/-- One charged transfer returns a fully loaded source and the restored
private store. No source instruction executes during this transfer. -/
theorem resume_transfer (key second : Machine.Tape) (saved machine : Machine.Configuration)
    (savedState state : State) (savedTrace trace : List (List Bool × List Bool))
    (request : List Bool) :
    TimedExecution.eval (step native code oracle) 1
      (.handling saved savedState savedTrace request (.calling key second (.source ⟨state, .running machine, trace⟩))) =
      PMF.pure (.source key ⟨state, .running machine, trace⟩) := by
  simp [TimedExecution.eval, step]

end CryptoOracle.Interactive.SourceEntry
