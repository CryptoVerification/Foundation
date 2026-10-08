import Foundation.Crypto.Semantics.Probability.Comp

/-! Quantitative indistinguishability relative to an explicit observer class.
No efficiency is inferred from a semantic observer predicate. A concrete
resource backend must justify membership of each composed observer. -/
namespace Foundation.Probability
open scoped ENNReal
universe u v

noncomputable def observerGap {Value : Type u} (left right : PMF Value)
    (observer : Value → PMF Bool) : ℝ≥0∞ :=
  probabilityGap (eventProb (left.bind observer) (· = true))
    (eventProb (right.bind observer) (· = true))

def ObserverBound {Value : Type u} (allowed : (Value → PMF Bool) → Prop)
    (left right : PMF Value) (epsilon : ℝ≥0∞) : Prop :=
  ∀ observer, allowed observer → observerGap left right observer ≤ epsilon

theorem observerGap_bind {Source : Type u} {Target : Type v}
    (left right : PMF Source) (kernel : Source → PMF Target) (observer : Target → PMF Bool) :
    observerGap (left.bind kernel) (right.bind kernel) observer =
      observerGap left right (fun source => (kernel source).bind observer) := by
  simp only [observerGap, PMF.bind_bind]

theorem ObserverBound.bind {Source : Type u} {Target : Type v}
    {sourceAllowed : (Source → PMF Bool) → Prop} {targetAllowed : (Target → PMF Bool) → Prop}
    {left right : PMF Source} {epsilon : ℝ≥0∞}
    (bound : ObserverBound sourceAllowed left right epsilon) (kernel : Source → PMF Target)
    (closed : ∀ observer, targetAllowed observer →
      sourceAllowed (fun source => (kernel source).bind observer)) :
    ObserverBound targetAllowed (left.bind kernel) (right.bind kernel) epsilon := by
  intro observer hObserver
  rw [observerGap_bind]
  exact bound _ (closed observer hObserver)

theorem ObserverBound.of_eq {Value : Type u} (allowed : (Value → PMF Bool) → Prop)
    {left right : PMF Value} (same : left = right) : ObserverBound allowed left right 0 := by
  subst right
  intro observer _
  simp [observerGap, probabilityGap]

end Foundation.Probability
