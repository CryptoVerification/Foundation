import Foundation.Crypto.Semantics.Probability.Facts
import Foundation.Crypto.Semantics.Probability.ObserverBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite total variation bounds every probabilistic observer. This is a
semantic contraction theorem, with no computational or novelty assertion. -/
namespace Foundation.Probability
open scoped BigOperators ENNReal

noncomputable def finiteVariation {α : Type} [Fintype α] (p q : PMF α) : ℝ :=
  (∑ a, |(p a).toReal - (q a).toReal|) / 2

theorem sum_real_mass {α : Type} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)] at h
  simpa using h

theorem centered_weight_bound {α : Type} [Fintype α] (d f : α → ℝ)
    (hd : ∑ a, d a = 0) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    |∑ a, d a * f a| ≤ (∑ a, |d a|) / 2 := by
  classical
  have hc : (∑ a, d a * f a) = ∑ a, d a * (f a - 1 / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd, zero_mul, sub_zero]
  rw [hc]
  calc
    _ ≤ ∑ a, |d a * (f a - 1 / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |d a| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hf a).1], by linarith [(hf a).2]⟩
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem event_bind_real {α β : Type} [Fintype α] (p : PMF α) (next : α → PMF β)
    (event : β → Prop) :
    (eventProb (p.bind next) event).toReal =
      ∑ a, (p a).toReal * (eventProb (next a) event).toReal := by
  rw [eventProb_bind_eq, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a)
      (ne_of_lt ((eventProb_le_one (next a) event).trans_lt (by simp)))

theorem probabilistic_event_real_bound {α β : Type} [Fintype α] (p q : PMF α)
    (next : α → PMF β) (event : β → Prop) :
    |(eventProb (p.bind next) event).toReal - (eventProb (q.bind next) event).toReal| ≤
      finiteVariation p q := by
  rw [event_bind_real, event_bind_real, ← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  apply centered_weight_bound
  · rw [Finset.sum_sub_distrib, sum_real_mass, sum_real_mass, sub_self]
  · intro a
    exact ⟨ENNReal.toReal_nonneg, by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (eventProb_le_one (next a) event)⟩

theorem probabilityGap_eq_ofReal_abs (p q : ℝ≥0∞) (hp : p ≠ ∞) (hq : q ≠ ∞) :
    probabilityGap p q = ENNReal.ofReal |p.toReal - q.toReal| := by
  have hsub (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
      a - b = ENNReal.ofReal (a.toReal - b.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
  unfold probabilityGap
  rw [hsub p q hp hq, hsub q p hq hp, ← ENNReal.ofReal_max, abs_eq_max_neg]
  congr 2
  ring

theorem probabilistic_event_bound {α β : Type} [Fintype α] (p q : PMF α)
    (next : α → PMF β) (event : β → Prop) :
    probabilityGap (eventProb (p.bind next) event) (eventProb (q.bind next) event) ≤
      ENNReal.ofReal (finiteVariation p q) := by
  rw [probabilityGap_eq_ofReal_abs _ _
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))]
  exact ENNReal.ofReal_le_ofReal (probabilistic_event_real_bound p q next event)

theorem all_observers_bound {α : Type} [Fintype α] (p q : PMF α) :
    ObserverBound (fun _ => True) p q (ENNReal.ofReal (finiteVariation p q)) := by
  intro observer _
  exact probabilistic_event_bound p q observer (· = true)

end Foundation.Probability
