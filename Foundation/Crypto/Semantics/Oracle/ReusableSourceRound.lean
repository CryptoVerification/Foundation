import Foundation.Crypto.Semantics.Oracle.ReusableSourceRequest
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureIteration

/-! A complete adaptive source round: run the actual caller to its next
request or termination, charge the transfer, execute the selected certified
service, and return its complete physical source configuration. -/
namespace CryptoOracle.Interactive.ReusableSourceRound
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)

abbrev Source := Saved × Configuration State
noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

def embed (source : Source (State := State) (Saved := Saved)) :
    ReusableResponseSource.Control Component State Saved := .source source.1 source.2

variable (service : ∀ (_retained : Saved) (_caller : Machine.Configuration) (_state : State)
    (_trace : List (List Bool × List Bool)) (_request : List Bool),
    Procedure (outerStep componentStep begin ready native code oracle) Unit (Source (State := State) (Saved := Saved)))
    (hEntry : ∀ retained caller state trace request,
      (service retained caller state trace request).entry () =
        .processing caller state trace request (begin retained request))
    (hExit : ∀ retained caller state trace request output,
      (service retained caller state trace request).exit () output = embed output)

noncomputable def transfer (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  Procedure.ofFixed (outerStep componentStep begin ready native code oracle)
    (fun _ : Unit => ReusableResponseSource.Control.source retained ⟨state, .awaiting caller request, trace⟩)
    (fun _ _ : Unit => .processing caller state trace request (begin retained request))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, PMF.pure_map])

noncomputable def selected (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  ((transfer componentStep begin ready native code oracle retained caller state trace request).seq
    (service retained caller state trace request)
    (fun argument middle _ => by cases argument; cases middle; exact hEntry retained caller state trace request)
    (fun _ => (service retained caller state trace request).budget ())
    (fun argument middle _ => by cases middle; exact Nat.le_refl _)).observe Prod.snd
    (fun _ output => embed output)
    (fun _argument output _ => by
      rcases output with ⟨⟨⟩, output⟩
      exact (hExit retained caller state trace request output).symm)

noncomputable def response (retained : Saved) (frame : Configuration State) :
    Procedure (outerStep componentStep begin ready native code oracle) Unit (Source (State := State) (Saved := Saved)) :=
  match frame.control with
  | .awaiting caller request =>
      selected componentStep begin ready native code oracle service hEntry hExit retained caller frame.state frame.reverseTrace request
  | _ => Procedure.ofFixed _ (fun _ => embed (retained, frame)) (fun _ output => embed output)
      (fun _ => PMF.pure (retained, frame)) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, PMF.pure_map])

theorem response_entry (retained : Saved) (frame : Configuration State) :
    (response componentStep begin ready native code oracle service hEntry hExit retained frame).entry () =
      embed (retained, frame) := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_exit (retained : Saved) (frame : Configuration State) (output : Source (State := State) (Saved := Saved)) :
    (response componentStep begin ready native code oracle service hEntry hExit retained frame).exit () output =
      embed output := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_budget (retained : Saved) (frame : Configuration State) :
    (response componentStep begin ready native code oracle service hEntry hExit retained frame).budget () =
      match frame.control with
      | .awaiting caller request => 1 + (service retained caller frame.state frame.reverseTrace request).budget ()
      | _ => 0 := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_semantics (retained : Saved) (frame : Configuration State) :
    (response componentStep begin ready native code oracle service hEntry hExit retained frame).semantics () =
      match frame.control with
      | .awaiting caller request => (service retained caller frame.state frame.reverseTrace request).semantics ()
      | _ => PMF.pure (retained, frame) := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> try rfl
  simp only [response, selected, Procedure.observe, Procedure.seq, transfer,
    TimedExecution.Procedure.ofFixed, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

variable (retained : Saved) (cap : SourcePrefix.Input code oracle → Nat)
    (hCap : ∀ input frame, frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support →
      ∀ caller request, frame.control = .awaiting caller request →
        (service retained caller frame.state frame.reverseTrace request).budget () ≤ cap input)

noncomputable def continuation :=
  Procedure.dispatch (response componentStep begin ready native code oracle service hEntry hExit retained)

noncomputable def combined :=
  (ReusableSourceRequest.procedure componentStep begin ready native code oracle retained).seq
    (continuation componentStep begin ready native code oracle service hEntry hExit retained)
    (fun _ frame _ => response_entry componentStep begin ready native code oracle service hEntry hExit retained frame)
    (fun input => 1 + cap input)
    (by
      intro input frame h
      change (response componentStep begin ready native code oracle service hEntry hExit retained frame).budget () ≤ _
      rw [response_budget]
      cases hc : frame.control with
      | awaiting caller request =>
          have hb := hCap input frame h caller request hc
          simp only
          omega
      | _ => simp only; omega)

noncomputable def round :=
  (combined componentStep begin ready native code oracle service hEntry hExit retained cap hCap).observe Prod.snd
    (fun _ output => embed output)
    (fun _ output _ => (response_exit componentStep begin ready native code oracle service hEntry hExit retained output.1 output.2).symm)

theorem round_entry (input : SourcePrefix.Input code oracle) :
    (round componentStep begin ready native code oracle service hEntry hExit retained cap hCap).entry input =
      embed (retained, input.start) := rfl

theorem round_exit (input : SourcePrefix.Input code oracle) (output : Source (State := State) (Saved := Saved)) :
    (round componentStep begin ready native code oracle service hEntry hExit retained cap hCap).exit input output =
      embed output := rfl

theorem round_budget (input : SourcePrefix.Input code oracle) :
    (round componentStep begin ready native code oracle service hEntry hExit retained cap hCap).budget input =
      input.budget + (1 + cap input) := rfl

theorem round_semantics (input : SourcePrefix.Input code oracle) :
    (round componentStep begin ready native code oracle service hEntry hExit retained cap hCap).semantics input =
      (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).bind
        (fun frame => (response componentStep begin ready native code oracle service hEntry hExit retained frame).semantics ()) := by
  simp only [round, combined, Procedure.observe, Procedure.seq, continuation, Procedure.dispatch,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [show (fun x : Source (State := State) (Saved := Saved) => x) = id by rfl]
  simp only [PMF.map_id]
  rfl

end CryptoOracle.Interactive.ReusableSourceRound
