import Foundation.Quantum.QKD.BinaryWeightVolume
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A generating-function bound on binary-ball volume, valid also when the
radius exceeds the number of coordinates. -/
namespace Foundation.Quantum.QKD.BinaryWeightVolume
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem weight_sum (n : Nat) (t : ℝ) :
    ∑ x : Fin n → Fin 2, t^(support x).card = (1+t)^n := by
  have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) t (1:ℝ)
  simp only [one_pow, mul_one, Fintype.card_fin] at h
  rw [add_comm] at h
  rw [← h]
  exact Fintype.sum_equiv (bitsEquiv n) _ _ (fun _ => rfl)

theorem volume_weighted (n radius : Nat) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume n radius : ℝ)*t^radius ≤ (1+t)^n := by
  classical
  calc
    _ = ∑ x ∈ ball n radius, t^radius := by simp [ball_card]
    _ ≤ ∑ x ∈ ball n radius, t^(support x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact pow_le_pow_of_le_one ht ht1 (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x : Fin n → Fin 2, t^(support x).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => pow_nonneg ht _)
    _ = _ := weight_sum n t

theorem volume_bound (n radius : Nat) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (volume n radius : ℝ) ≤ (1+t)^n / t^radius := by
  exact (le_div_iff₀ (pow_pos ht _)).mpr (volume_weighted n radius t ht.le ht1)

/-- A rational exponential bound; no logarithm or entropy assumption. -/
theorem volume_quarter (n radius : Nat) :
    (volume n radius : ℝ) ≤ (5/4:ℝ)^n * 4^radius := by
  have h := volume_bound n radius (1/4:ℝ) (by norm_num) (by norm_num)
  norm_num only [show (1+1/4:ℝ) = 5/4 by norm_num] at h
  simpa only [div_eq_mul_inv, inv_pow, inv_div, div_one, one_mul, inv_inv] using h

end
end Foundation.Quantum.QKD.BinaryWeightVolume
