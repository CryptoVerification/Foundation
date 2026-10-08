import Foundation.Crypto.Semantics.ProcedureCostObservation

/-! A fixed supported contract cost determines the exact execution law at
that cost, provided the residual law is available there. Intermediate exits
need not be absorbing: this also applies immediately before a caller halt. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Input : Type v} {Output : Type w}
    {step : State → PMF State} (P : Procedure step Input Output)

theorem eval_at_fixed_time (input : Input) (duration : Nat)
    (bounded : P.budget input ≤ duration)
    (fixed : ∀ result, result ∈ (P.costed input).support → result.2 = duration) :
    eval step duration (P.entry input) = (P.semantics input).map (P.exit input) := by
  rw [P.law input duration bounded, ← P.correct input, PMF.map_comp]
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  rw [fixed result hResult, Nat.sub_self]
  rfl

end Foundation.Probability.TimedExecution.Procedure
