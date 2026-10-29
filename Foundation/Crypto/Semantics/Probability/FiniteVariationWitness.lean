import Foundation.Crypto.Semantics.Probability.FiniteObserverVariation

/-! A Boolean observation attains finite total variation. The test is semantic;
this file does not assert an efficient native implementation of the test. -/
namespace Foundation.Probability
open scoped BigOperators ENNReal

theorem finiteVariation_nonneg {α : Type} [Fintype α] (p q : PMF α) :
    0 ≤ finiteVariation p q := by
  unfold finiteVariation
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg _)) (by norm_num)

theorem positive_sum_eq_half_abs {α : Type} [Fintype α] (d : α → ℝ)
    (hd : ∑ a, d a = 0) :
    (∑ a, if 0 ≤ d a then d a else 0) = (∑ a, |d a|) / 2 := by
  classical
  have hterm (a : α) : 2 * (if 0 ≤ d a then d a else 0) = |d a| + d a := by
    by_cases h : 0 ≤ d a
    · rw [if_pos h, abs_of_nonneg h]; ring
    · rw [if_neg h, abs_of_neg (lt_of_not_ge h)]; ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => hterm a)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hd, add_zero] at hsum
  linarith

theorem event_real_sum {α : Type} [Fintype α] (p : PMF α) (event : α → Prop) [DecidablePred event] :
    (eventProb p event).toReal = ∑ a, if event a then (p a).toReal else 0 := by
  classical
  rw [eventProb, PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : event a <;> simp [Set.indicator_apply, h]
  · intro a _
    by_cases h : event a <;> simp [Set.indicator_apply, h, p.apply_ne_top a]

noncomputable def positiveTest {α : Type} (p q : PMF α) (a : α) : Bool := by
  classical
  exact decide ((q a).toReal ≤ (p a).toReal)

theorem positiveTest_real_difference {α : Type} [Fintype α] (p q : PMF α) :
    (eventProb (p.map (positiveTest p q)) (· = true)).toReal -
      (eventProb (q.map (positiveTest p q)) (· = true)).toReal = finiteVariation p q := by
  classical
  rw [eventProb_map, eventProb_map, event_real_sum, event_real_sum, ← Finset.sum_sub_distrib]
  have ht (a : α) :
      (if positiveTest p q a = true then (p a).toReal else 0) -
        (if positiveTest p q a = true then (q a).toReal else 0) =
      if 0 ≤ (p a).toReal - (q a).toReal then (p a).toReal - (q a).toReal else 0 := by
    by_cases h : (q a).toReal ≤ (p a).toReal <;> simp [positiveTest, h, sub_nonneg]
  simp_rw [ht]
  exact positive_sum_eq_half_abs _ (by rw [Finset.sum_sub_distrib, sum_real_mass, sum_real_mass, sub_self])

theorem positiveTest_attains {α : Type} [Fintype α] (p q : PMF α) :
    probabilityGap (eventProb (p.map (positiveTest p q)) (· = true))
      (eventProb (q.map (positiveTest p q)) (· = true)) = ENNReal.ofReal (finiteVariation p q) := by
  rw [probabilityGap_eq_ofReal_abs _ _
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp))),
    positiveTest_real_difference, abs_of_nonneg (finiteVariation_nonneg p q)]

end Foundation.Probability
