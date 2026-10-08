import Foundation.Crypto.Semantics.Oracle.CallerRound

/-! Joint result/time laws for response-independent caller composition.
Selection costs are first-arrival times. Branch-dependent service costs
remain correlated with selected requests and returned physical frames. -/
namespace CryptoOracle.Interactive.CallerRuntime.Runtime
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Saved : Type v} {Target : Type w}
    {code : Code} {oracle : BitOracle State} (R : Runtime Saved Target code oracle)
    (service : ∀ (_retained : Saved) (_caller : Machine.Configuration) (_state : State)
      (_trace : List (List Bool × List Bool)) (_request : List Bool),
      Procedure R.step Unit (Source (State := State) (Saved := Saved)))
    (hEntry : ∀ retained caller state trace request,
      (service retained caller state trace request).entry () = R.request retained caller state trace request)
    (hExit : ∀ retained caller state trace request output,
      (service retained caller state trace request).exit () output = R.source output)

theorem prefix_costed (retained : Saved) (input : SourcePrefix.Input code oracle) :
    (R.selection retained).costed input =
      runToBoundary (SourcePrefix.step code oracle) SourcePrefix.boundary input.budget input.start := by
  change (runToBoundary _ _ _ _).map (fun result => (result.1, result.2)) = _
  exact PMF.map_id _

/-- Awaiting calls charge one ownership transfer before the service.
Already terminal branches incur no response cost. -/
theorem response_costed (retained : Saved) (frame : Configuration State) :
    (R.response service hEntry hExit retained frame).costed () =
      match frame.control with
      | .awaiting caller request =>
          ((service retained caller frame.state frame.reverseTrace request).costed ()).map
            (fun result => (result.1, 1 + result.2))
      | _ => PMF.pure ((retained, frame), 0) := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;>
    simp only [response, selected, Procedure.observe, Procedure.seq, transfer,
      Procedure.ofFixed, PMF.pure_bind, PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]

/-- First selection and response costs are added on each actual branch. -/
theorem roundAt_costed (retained : Saved) (input : SourcePrefix.Input code oracle) (cap : Nat)
    (hCap : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support,
      ∀ caller request, frame.control = .awaiting caller request →
        (service retained caller frame.state frame.reverseTrace request).budget () ≤ cap) :
    (R.roundAt service hEntry hExit retained input cap hCap).costed () =
      (runToBoundary (SourcePrefix.step code oracle) SourcePrefix.boundary input.budget input.start).bind
        (fun selected => ((R.response service hEntry hExit retained selected.1).costed ()).map
          (fun result => (result.1, selected.2 + result.2))) := by
  simp only [roundAt, Procedure.observe, Procedure.seq, Procedure.dispatch,
    Procedure.reindex, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [prefix_costed]

end CryptoOracle.Interactive.CallerRuntime.Runtime
