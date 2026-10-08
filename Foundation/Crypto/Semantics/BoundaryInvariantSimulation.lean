import Foundation.Crypto.Semantics.TimedExecution

/-! Boundary simulation needs a one-step correspondence only on supported
valid states before the boundary. No global correspondence on malformed
states or continuation instructions is required. Exact costs are retained. -/
namespace Foundation.Probability.TimedExecution
universe u v
variable {Source : Type u} {Target : Type v}

theorem runToBoundary_map_on_invariant
    (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceBoundary : Source → Bool) (targetBoundary : Target → Bool)
    (embed : Source → Target) (valid : Source → Prop)
    (preserves : ∀ source, valid source → sourceBoundary source = false →
      ∀ next, next ∈ (sourceStep source).support → valid next)
    (sameBoundary : ∀ source, valid source → targetBoundary (embed source) = sourceBoundary source)
    (sameStep : ∀ source, valid source → sourceBoundary source = false →
      targetStep (embed source) = (sourceStep source).map embed)
    (fuel : Nat) (start : Source) (hValid : valid start) :
    runToBoundary targetStep targetBoundary fuel (embed start) =
      (runToBoundary sourceStep sourceBoundary fuel start).map (fun result => (embed result.1, result.2)) := by
  induction fuel generalizing start with
  | zero => simp [runToBoundary, PMF.pure_map]
  | succ fuel ih =>
      cases hBoundary : sourceBoundary start with
      | true => simp [runToBoundary, sameBoundary start hValid, hBoundary, PMF.pure_map]
      | false =>
          simp only [runToBoundary, sameBoundary start hValid, hBoundary, Bool.false_eq_true, ↓reduceIte,
            sameStep start hValid hBoundary, PMF.bind_map, PMF.map_bind]
          rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
          congr 1
          funext next hNext
          dsimp only [Function.comp_def]
          rw [ih next (preserves start hValid hBoundary next hNext), PMF.map_comp, PMF.map_comp]
          rfl

end Foundation.Probability.TimedExecution
