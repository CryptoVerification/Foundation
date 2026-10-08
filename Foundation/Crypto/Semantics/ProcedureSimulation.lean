import Foundation.Crypto.Semantics.Procedure
import Foundation.Crypto.Semantics.Simulation

/-! Transport a complete execution contract along an exact step simulation.
This adds neither runtime preparation nor cost-free controller transitions. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {State : Type u} {Target : Type v} {Input : Type w} {Output : Type x}
    {sourceStep : State → PMF State}

noncomputable def transport (P : Procedure sourceStep Input Output)
    (targetStep : Target → PMF Target) (embed : State → Target)
    (hStep : ∀ state, targetStep (embed state) = (sourceStep state).map embed) :
    Procedure targetStep Input Output where
  entry := fun input => embed (P.entry input)
  exit := fun input output => embed (P.exit input output)
  semantics := P.semantics
  costed := P.costed
  budget := P.budget
  bounded := P.bounded
  correct := P.correct
  law := by
    intro input horizon hBudget
    rw [← eval_map sourceStep targetStep embed (fun state => (hStep state).symm), P.law input horizon hBudget, PMF.map_bind]
    congr 1
    funext result
    exact eval_map sourceStep targetStep embed (fun state => (hStep state).symm) _ _

end Foundation.Probability.TimedExecution.Procedure
