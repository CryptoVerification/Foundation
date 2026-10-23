import Foundation.Crypto.Semantics.Probability.SharedEventBudget
import Foundation.Crypto.Semantics.Probability.Copyability

/-! Identical written labels cannot merge bad events from independent runs.
A common-event budget therefore requires an actual joint realization. -/
namespace Foundation.Examples.SharedEventBudgetIndependence
open Foundation.Probability
open scoped ENNReal

noncomputable def independent : ProbComp (Bool × Bool) := Copyability.independent (uniform Bool) (uniform Bool)

theorem independent_failure : eventProb independent (fun pair => pair.1 = true ∨ pair.2 = true) = 3 / 4 := by
  rw [independent, Copyability.independent, uniform_pair]
  simp [eventProb, uniform, Set.indicator_apply, Fintype.sum_prod_type]
  simp only [div_eq_mul_inv]
  ring

theorem shared_failure : eventProb (Copyability.shared (uniform Bool)) (fun pair => pair.1 = true ∨ pair.2 = true) = 1 / 2 := by
  rw [Copyability.shared, eventProb_map]
  simpa only [or_self, Fintype.card_bool, Nat.cast_ofNat, one_div] using uniform_guess (α := Bool) true

theorem cannot_merge_independent : ¬ eventProb independent (fun pair => pair.1 = true ∨ pair.2 = true) ≤ 1 / 2 := by
  rw [independent_failure]
  intro bound
  have realBound := ENNReal.toReal_mono (by finiteness : (1 / 2 : ℝ≥0∞) ≠ ⊤) bound
  norm_num at realBound

end Foundation.Examples.SharedEventBudgetIndependence
