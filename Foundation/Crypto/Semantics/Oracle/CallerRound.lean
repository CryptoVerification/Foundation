import Foundation.Crypto.Semantics.Oracle.CallerRuntime
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureIteration

/-! A response-independent caller round: execute real source code to its
next request or halt, transfer ownership, execute a certified service, and
return the complete actual caller. Branches and costs remain probabilistic. -/
namespace CryptoOracle.Interactive.CallerRuntime.Runtime
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Saved : Type v} {Target : Type w}
    {code : Code} {oracle : BitOracle State} (R : Runtime Saved Target code oracle)
    (service : ∀ (_retained : Saved) (_caller : Machine.Configuration) (_state : State)
      (_trace : List (List Bool × List Bool)) (_request : List Bool), Procedure R.step Unit (Source (State := State) (Saved := Saved)))
    (hEntry : ∀ retained caller state trace request,
      (service retained caller state trace request).entry () = R.request retained caller state trace request)
    (hExit : ∀ retained caller state trace request output,
      (service retained caller state trace request).exit () output = R.source output)

noncomputable def selected (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  ((R.transfer retained caller state trace request).seq (service retained caller state trace request)
    (fun argument middle _ => by cases argument; cases middle; exact hEntry retained caller state trace request)
    (fun _ => (service retained caller state trace request).budget ())
    (fun _ middle _ => by cases middle; exact Nat.le_refl _)).observe Prod.snd
    (fun _ output => R.source output)
    (fun _ output _ => by rcases output with ⟨⟨⟩, output⟩; exact (hExit retained caller state trace request output).symm)

noncomputable def response (retained : Saved) (frame : Configuration State) :
    Procedure R.step Unit (Source (State := State) (Saved := Saved)) :=
  match frame.control with
  | .awaiting caller request => R.selected service hEntry hExit retained caller frame.state frame.reverseTrace request
  | _ => Procedure.ofFixed _ (fun _ => R.embed retained frame) (fun _ output => R.source output)
      (fun _ => PMF.pure (retained, frame)) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, source, PMF.pure_map])

theorem response_entry (retained : Saved) (frame : Configuration State) :
    (R.response service hEntry hExit retained frame).entry () = R.embed retained frame := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_exit (retained : Saved) (frame : Configuration State) (output : Source (State := State) (Saved := Saved)) :
    (R.response service hEntry hExit retained frame).exit () output = R.source output := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_budget (retained : Saved) (frame : Configuration State) :
    (R.response service hEntry hExit retained frame).budget () =
      match frame.control with
      | .awaiting caller request => 1 + (service retained caller frame.state frame.reverseTrace request).budget ()
      | _ => 0 := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> rfl

theorem response_semantics (retained : Saved) (frame : Configuration State) :
    (R.response service hEntry hExit retained frame).semantics () =
      match frame.control with
      | .awaiting caller request => (service retained caller frame.state frame.reverseTrace request).semantics ()
      | _ => PMF.pure (retained, frame) := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> try rfl
  simp only [response, selected, Procedure.observe, Procedure.seq, transfer,
    Procedure.ofFixed, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- Specialize one physical selection. Bounds need hold only for its
reachable choices, rather than for every unrelated source input. -/
noncomputable def roundAt (retained : Saved) (input : SourcePrefix.Input code oracle) (cap : Nat)
    (hCap : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support,
      ∀ caller request, frame.control = .awaiting caller request →
        (service retained caller frame.state frame.reverseTrace request).budget () ≤ cap) :=
  (((R.selection retained).reindex (fun _ : Unit => input)).seq
    (Procedure.dispatch (R.response service hEntry hExit retained))
    (fun _ frame _ => R.response_entry service hEntry hExit retained frame)
    (fun _ => 1 + cap) (by
      intro _ frame h
      change (R.response service hEntry hExit retained frame).budget () ≤ _
      rw [response_budget]
      cases hc : frame.control with
      | awaiting caller request =>
          have hb := hCap frame h caller request hc
          simp only
          omega
      | _ => simp only; omega)).observe Prod.snd
    (fun _ output => R.source output)
    (fun _ output _ => (R.response_exit service hEntry hExit retained output.1 output.2).symm)

theorem roundAt_semantics (retained : Saved) (input : SourcePrefix.Input code oracle) (cap : Nat)
    (hCap : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support,
      ∀ caller request, frame.control = .awaiting caller request →
        (service retained caller frame.state frame.reverseTrace request).budget () ≤ cap) :
    (R.roundAt service hEntry hExit retained input cap hCap).semantics () =
      (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).bind
        (fun frame => (R.response service hEntry hExit retained frame).semantics ()) := by
  simp only [roundAt, Procedure.observe, Procedure.seq, Procedure.dispatch,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [show (fun x : Source (State := State) (Saved := Saved) => x) = id by rfl]
  simp only [PMF.map_id]
  rfl

variable (retained : Saved) (cap : SourcePrefix.Input code oracle → Nat)
    (hCap : ∀ input frame, frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support →
      ∀ caller request, frame.control = .awaiting caller request →
        (service retained caller frame.state frame.reverseTrace request).budget () ≤ cap input)

noncomputable def combined :=
  (R.selection retained).seq (Procedure.dispatch (R.response service hEntry hExit retained))
    (fun _ frame _ => R.response_entry service hEntry hExit retained frame)
    (fun input => 1 + cap input)
    (by
      intro input frame h
      change (R.response service hEntry hExit retained frame).budget () ≤ _
      rw [response_budget]
      cases hc : frame.control with
      | awaiting caller request =>
          have hb := hCap input frame h caller request hc
          simp only
          omega
      | _ => simp only; omega)

noncomputable def round :=
  (R.combined service hEntry hExit retained cap hCap).observe Prod.snd
    (fun _ output => R.source output)
    (fun _ output _ => (R.response_exit service hEntry hExit retained output.1 output.2).symm)

theorem round_entry (input : SourcePrefix.Input code oracle) :
    (R.round service hEntry hExit retained cap hCap).entry input = R.embed retained input.start := rfl

theorem round_exit (input : SourcePrefix.Input code oracle) (output : Source (State := State) (Saved := Saved)) :
    (R.round service hEntry hExit retained cap hCap).exit input output = R.source output := rfl

theorem round_budget (input : SourcePrefix.Input code oracle) :
    (R.round service hEntry hExit retained cap hCap).budget input = input.budget + (1 + cap input) := rfl

theorem round_semantics (input : SourcePrefix.Input code oracle) :
    (R.round service hEntry hExit retained cap hCap).semantics input =
      (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).bind
        (fun frame => (R.response service hEntry hExit retained frame).semantics ()) := by
  simp only [round, combined, Procedure.observe, Procedure.seq, Procedure.dispatch,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [show (fun x : Source (State := State) (Saved := Saved) => x) = id by rfl]
  simp only [PMF.map_id]
  rfl

end CryptoOracle.Interactive.CallerRuntime.Runtime
