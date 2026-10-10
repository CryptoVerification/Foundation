import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.Oracle.SourcePrefix

/-! Capture arbitrary adaptive source requests in the reusable controller.
Source execution cannot consult the private store. Finite procedure fuel is
kept distinct from a certificate of reaching a request or termination. -/
namespace CryptoOracle.Interactive.ReusableSourceRequest
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (retained : Saved)

noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

def boundary : ReusableResponseSource.Control Component State Saved → Bool
  | .source _ frame => SourcePrefix.boundary frame
  | _ => true

noncomputable def procedure :=
  SourcePrefix.liftTo code oracle (outerStep componentStep begin ready native code oracle) boundary
    (ReusableResponseSource.Control.source retained) (fun _ => rfl)
    (by intro frame h; cases hc : frame.control <;>
      simp_all [SourcePrefix.boundary, SourcePrefix.step, outerStep, ReusableResponseSource.step])

theorem prefix_budget (input : SourcePrefix.Input code oracle) :
    (procedure componentStep begin ready native code oracle retained).budget input = input.budget := rfl

theorem prefix_distribution (input : SourcePrefix.Input code oracle) :
    ((procedure componentStep begin ready native code oracle retained).costed input).map Prod.fst =
      TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start :=
  (procedure componentStep begin ready native code oracle retained).correct input

/-- Both the chosen request and its real first-arrival cost are independent
of the retained private value. Previous public replies remain in the frame. -/
theorem prefix_private_independence (first second : Saved) (input : SourcePrefix.Input code oracle) :
    (procedure componentStep begin ready native code oracle first).costed input =
      (procedure componentStep begin ready native code oracle second).costed input := rfl

theorem collect (key : Saved) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (bits reversed : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (bits.length + 1)
      (.source key ⟨state, .sending machine (RequestExport.packetTape before after bits) reversed, trace⟩) =
      PMF.pure (.source key ⟨state, .reversing machine (bits.reverse ++ reversed) [], trace⟩) := by
  induction bits generalizing reversed before with
  | nil =>
      simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, PMF.pure_map]
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [outerStep, ReusableResponseSource.step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, List.map_cons,
        List.cons_append, List.headD_cons, List.tail_cons, Machine.Tape.moveRight, PMF.pure_map, PMF.pure_bind]
      cases bits <;> simpa [RequestExport.packetTape, List.reverse_cons, List.append_assoc]
        using ih (bit :: reversed) (some bit :: before)

theorem reverse (key : Saved) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (remaining.length + 1)
      (.source key ⟨state, .reversing machine remaining request, trace⟩) =
      PMF.pure (.source key ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩) := by
  induction remaining generalizing request with
  | nil =>
      simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [outerStep, ReusableResponseSource.step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem export_run (key : Saved) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (2 * request.length + 2)
      (.source key ⟨state, .sending machine (RequestExport.packetTape before after request) [], trace⟩) =
      PMF.pure (.source key ⟨state, .awaiting machine request, trace⟩) := by
  rw [show 2 * request.length + 2 = (request.length + 1) + (request.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse]
  simp

/-- Actual request capture, export and a charged transfer to the component. -/
theorem capture_run (key : Saved) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (2 * request.length + 4)
      (.source key ⟨state, .running machine, trace⟩) =
      PMF.pure (.processing machine.advance state trace request (begin key request)) := by
  rw [show 2 * request.length + 4 = ((2 * request.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [outerStep, ReusableResponseSource.step, Reification.timedStep, Reification.terminal, hActive, Bool.false_eq_true, ↓reduceIte,
    Reification.perform, Reification.action, transition, hCall, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (outerStep componentStep begin ready native code oracle) (2 * request.length + 2) 1]
  rw [hTape, export_run, PMF.pure_bind]
  simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, Machine.Configuration.advance, hTape]


end CryptoOracle.Interactive.ReusableSourceRequest
