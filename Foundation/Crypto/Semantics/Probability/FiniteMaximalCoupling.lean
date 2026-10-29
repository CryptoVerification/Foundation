import Foundation.Crypto.Semantics.Probability.FiniteObserverVariation
import Foundation.Crypto.Semantics.Probability.Coupling

/-! A finite maximal coupling with an explicit joint mass. Common mass stays
on the diagonal; the two disjoint residuals are coupled independently. This
is a semantic construction and assigns no runtime to sampling the coupling. -/
namespace Foundation.Probability.FiniteMaximalCoupling
open scoped BigOperators ENNReal
noncomputable section
variable {α : Type} [Fintype α] (p q : PMF α)
local instance : DecidableEq α := Classical.decEq α

def common (x : α) : ℝ := min (p x).toReal (q x).toReal
def left (x : α) : ℝ := (p x).toReal - common p q x
def right (x : α) : ℝ := (q x).toReal - common p q x
def residual : ℝ := 1 - ∑ x, common p q x

omit [Fintype α] in
theorem common_nonneg (x : α) : 0 ≤ common p q x := le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
omit [Fintype α] in
theorem left_nonneg (x : α) : 0 ≤ left p q x := sub_nonneg.mpr (min_le_left _ _)
omit [Fintype α] in
theorem right_nonneg (x : α) : 0 ≤ right p q x := sub_nonneg.mpr (min_le_right _ _)
theorem sum_left : ∑ x, left p q x = residual p q := by
  simp only [left, Finset.sum_sub_distrib, sum_real_mass, residual]
theorem sum_right : ∑ x, right p q x = residual p q := by
  simp only [right, Finset.sum_sub_distrib, sum_real_mass, residual]
theorem residual_nonneg : 0 ≤ residual p q := by
  rw [← sum_left]
  exact Finset.sum_nonneg (fun x _ => left_nonneg p q x)
theorem left_zero (h : residual p q = 0) (x : α) : left p q x = 0 := by
  have hs := sum_left p q
  rw [h] at hs
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => left_nonneg p q x)).mp hs x (Finset.mem_univ _)
theorem right_zero (h : residual p q = 0) (x : α) : right p q x = 0 := by
  have hs := sum_right p q
  rw [h] at hs
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => right_nonneg p q x)).mp hs x (Finset.mem_univ _)
omit [Fintype α] in
theorem disjoint (x : α) : left p q x * right p q x = 0 := by
  unfold left right common
  rcases le_total (p x).toReal (q x).toReal with h | h
  · rw [min_eq_left h, sub_self, zero_mul]
  · rw [min_eq_right h, sub_self, mul_zero]

def mass (x y : α) : ℝ :=
  (if x = y then common p q x else 0) + left p q x * right p q y / residual p q

theorem mass_nonneg (x y : α) : 0 ≤ mass p q x y := by
  classical
  exact add_nonneg (by split_ifs; exact common_nonneg p q x; rfl)
    (div_nonneg (mul_nonneg (left_nonneg p q x) (right_nonneg p q y)) (residual_nonneg p q))

theorem row_sum (x : α) : ∑ y, mass p q x y = (p x).toReal := by
  classical
  simp only [mass, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, sum_right]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : residual p q = 0
  · have hz := left_zero p q h x
    simp only [h, div_zero, add_zero]
    unfold left at hz
    linarith
  · rw [mul_div_cancel_right₀ _ h]
    simp only [left]
    ring

theorem col_sum (y : α) : ∑ x, mass p q x y = (q y).toReal := by
  classical
  simp only [mass, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, sum_left]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : residual p q = 0
  · have hz := right_zero p q h y
    simp only [h, zero_mul, zero_div, add_zero]
    unfold right at hz
    linarith
  · rw [mul_div_cancel_left₀ _ h]
    simp only [right]
    ring

theorem diagonal (x : α) : mass p q x x = common p q x := by
  simp [mass, disjoint]

theorem total_mass : ∑ pair : α × α, mass p q pair.1 pair.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [row_sum, sum_real_mass]

def joint : PMF (α × α) := PMF.ofFintype
  (fun pair => ENNReal.ofReal (mass p q pair.1 pair.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun pair _ => mass_nonneg p q pair.1 pair.2), total_mass]
    simp)

theorem joint_real (x y : α) : (joint p q (x,y)).toReal = mass p q x y := by
  exact ENNReal.toReal_ofReal (mass_nonneg p q x y)

theorem joint_left : (joint p q).map Prod.fst = p := by
  classical
  ext x
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  have hs (a : α) : (∑ b, if x = a then joint p q (a,b) else 0) =
      if x = a then ∑ b, joint p q (a,b) else 0 := by
    by_cases h : x = a <;> simp [h]
  simp_rw [hs]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ y, ENNReal.ofReal (mass p q x y)) = p x
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => mass_nonneg p q x y), row_sum,
    ENNReal.ofReal_toReal (p.apply_ne_top x)]

theorem joint_right : (joint p q).map Prod.snd = q := by
  classical
  ext y
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  have hs (b : α) : (∑ a, if y = b then joint p q (a,b) else 0) =
      if y = b then ∑ a, joint p q (a,b) else 0 := by
    by_cases h : y = b <;> simp [h]
  simp_rw [hs]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ x, ENNReal.ofReal (mass p q x y)) = q y
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mass_nonneg p q x y), col_sum,
    ENNReal.ofReal_toReal (q.apply_ne_top y)]

theorem residual_eq_variation : residual p q = finiteVariation p q := by
  have h (x : α) : |(p x).toReal - (q x).toReal| = left p q x + right p q x := by
    unfold left right common
    rcases le_total (p x).toReal (q x).toReal with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  unfold finiteVariation
  simp_rw [h]
  rw [Finset.sum_add_distrib, sum_left, sum_right]
  ring

theorem mismatch_probability : eventProb (joint p q) (fun pair => pair.1 ≠ pair.2) =
    ENNReal.ofReal (finiteVariation p q) := by
  classical
  have he : ∑ pair : α × α, (if pair.1 ≠ pair.2 then mass p q pair.1 pair.2 else 0) = residual p q := by
    have hh (pair : α × α) : (if pair.1 ≠ pair.2 then mass p q pair.1 pair.2 else 0) =
        mass p q pair.1 pair.2 - (if pair.1 = pair.2 then common p q pair.1 else 0) := by
      by_cases h : pair.1 = pair.2
      · simp [h, diagonal]
      · simp [h]
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, total_mass, Fintype.sum_prod_type]
    simp [residual]
  unfold eventProb
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  change (∑ pair : α × α, if pair.1 ≠ pair.2 then ENNReal.ofReal (mass p q pair.1 pair.2) else 0) = _
  simp_rw [← ENNReal.ofReal_zero, ← apply_ite ENNReal.ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun pair _ => by split_ifs; exact mass_nonneg p q _ _; rfl),
    he, residual_eq_variation]

end
end Foundation.Probability.FiniteMaximalCoupling
