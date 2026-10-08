import Foundation.Crypto.Semantics.Procedure

/-! A constant reported cost yields the logical view/cost joint law.
The support hypothesis is an equality of costs, not merely a common upper
bound. Physical arrival at this cost is a separate Operational obligation. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {State : Type u} {Input : Type v} {Output : Type w} {Value : Type x}
    {step : State → PMF State} (P : Procedure step Input Output)

theorem costed_view_of_fixed_time (view : Input → Output → Value) (input : Input) (duration : Nat)
    (fixed : ∀ result, result ∈ (P.costed input).support → result.2 = duration) :
    (P.costed input).map (fun result => (view input result.1, result.2)) =
      ((P.semantics input).map (view input)).map (fun value => (value, duration)) := by
  calc
    _ = (P.costed input).map (fun result => (view input result.1, duration)) := by
      rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext result hResult
      change PMF.pure (view input result.1, result.2) = PMF.pure (view input result.1, duration)
      rw [fixed result hResult]
    _ = _ := by
      rw [← P.correct, PMF.map_comp, PMF.map_comp]
      rfl

theorem costed_view_eq_of_fixed_time (view : Input → Output → Value) (left right : Input) (duration : Nat)
    (fixedLeft : ∀ result, result ∈ (P.costed left).support → result.2 = duration)
    (fixedRight : ∀ result, result ∈ (P.costed right).support → result.2 = duration)
    (sameView : (P.semantics left).map (view left) = (P.semantics right).map (view right)) :
    (P.costed left).map (fun result => (view left result.1, result.2)) =
      (P.costed right).map (fun result => (view right result.1, result.2)) := by
  rw [P.costed_view_of_fixed_time view left duration fixedLeft,
    P.costed_view_of_fixed_time view right duration fixedRight, sameView]

end Foundation.Probability.TimedExecution.Procedure
