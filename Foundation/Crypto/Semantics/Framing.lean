import Foundation.Crypto.Semantics.Procedure
import Foundation.Crypto.Semantics.Simulation

/-! Isolate a component from a retained caller frame. The component step
receives only its own state; the caller frame is carried unchanged. Framing
is an entry precondition, not a claim that copying or preparing tapes is free. -/
namespace Foundation.Probability.TimedExecution
universe u v w x
variable {State : Type u} {Saved : Type v} {Input : Type w} {Output : Type x}

noncomputable def framedStep (step : State → PMF State) (frame : State × Saved) : PMF (State × Saved) :=
  (step frame.1).map (fun next => (next, frame.2))

theorem framed_eval (step : State → PMF State) (fuel : Nat) (state : State) (saved : Saved) :
    eval (framedStep step) fuel (state, saved) =
      (eval step fuel state).map (fun next => (next, saved)) := by
  symm
  exact eval_map step (framedStep step) (fun next => (next, saved)) (fun _ => rfl) fuel state

theorem framed_saved (step : State → PMF State) (fuel : Nat) (state : State) (saved : Saved)
    (final : State × Saved) (h : final ∈ (eval (framedStep step) fuel (state, saved)).support) :
    final.2 = saved := by
  rw [framed_eval, PMF.mem_support_map_iff] at h
  obtain ⟨next, _, he⟩ := h
  subst final
  rfl

/-- The component's marginal execution cannot depend on the retained frame.
This is stronger than preservation of the frame's final contents alone. -/
theorem framed_local (step : State → PMF State) (fuel : Nat) (state : State) (saved : Saved) :
    (eval (framedStep step) fuel (state, saved)).map Prod.fst = eval step fuel state := by
  rw [framed_eval, PMF.map_comp]
  exact PMF.map_id _

namespace Procedure
variable {step : State → PMF State}

/-- Retain an arbitrary caller frame without exposing it to the component.
The component's costs and complete physical endpoints are unchanged. -/
noncomputable def frame (P : Procedure step Input Output) (Saved : Type v) :
    Procedure (framedStep (Saved := Saved) step) (Input × Saved) Output where
  entry := fun input => (P.entry input.1, input.2)
  exit := fun input output => (P.exit input.1 output, input.2)
  semantics := fun input => P.semantics input.1
  costed := fun input => P.costed input.1
  budget := fun input => P.budget input.1
  bounded := fun input => P.bounded input.1
  correct := fun input => P.correct input.1
  law := by
    intro input horizon hBudget
    rw [framed_eval, P.law input.1 horizon hBudget, PMF.map_bind]
    congr 1
    funext result
    exact (framed_eval step (horizon - result.2) (P.exit input.1 result.1) input.2).symm

end Procedure
end Foundation.Probability.TimedExecution
