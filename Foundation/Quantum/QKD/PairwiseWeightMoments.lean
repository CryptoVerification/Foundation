import Foundation.Quantum.QKD.PairwiseWeightDeviation

/-! Exact first-component variance from Bouman--Fehr Appendix B.5.
Only pairs with unequal entries contribute. Equal pairs may have arbitrary
values and all input errors may be correlated. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

def mixedCount {n : Nat} (q : Pattern n) : Nat :=
  (Finset.univ.filter (fun i => q (i,0) ≠ q (i,1))).card

theorem signedBit_square {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) (i : Fin n) :
    signedBit q s i ^ 2 = if q (i,0) ≠ q (i,1) then 1 else 0 := by
  have hs : s i = 0 ∨ s i = 1 := by
    have hh := (s i).isLt
    rcases (show (s i).val = 0 ∨ (s i).val = 1 by omega) with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  generalize h0 : q (i,0) = b0
  generalize h1 : q (i,1) = b1
  fin_cases b0 <;> fin_cases b1 <;> rcases hs with hs | hs <;>
    norm_num [signedBit, hs, flip, h0, h1]

theorem mixedCount_le {n : Nat} (q : Pattern n) : mixedCount q ≤ n := by
  simpa only [mixedCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => q (i,0) ≠ q (i,1))

/-- Exact unnormalized second moment; no concentration assumption is used. -/
theorem weightDifference_second_moment_exact {n : Nat} (q : Pattern n) :
    (∑ s : Fin n → Fin 2, weightDifference q s ^ 2) =
      (Fintype.card (Fin n → Fin 2) : ℝ) * mixedCount q := by
  have hexpand : (∑ s : Fin n → Fin 2, weightDifference q s ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ s : Fin n → Fin 2, signedBit q s i * signedBit q s j := by
    simp only [weightDifference, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hexpand]
  have hdiag (i : Fin n) :
      (∑ j : Fin n, ∑ s : Fin n → Fin 2, signedBit q s i * signedBit q s j) =
        ∑ s : Fin n → Fin 2, signedBit q s i ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp only [pow_two]
    · intro j _ hji
      exact cross_sum_zero q i j hji
    · simp
  simp_rw [hdiag, signedBit_square]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_boole]
  rfl

/-- Exact normalized variance equals the number of unequal pairs. -/
theorem weightDifference_uniform_second_moment_exact {n : Nat} (q : Pattern n) :
    (∑ s : Fin n → Fin 2, (Foundation.Probability.uniform (Fin n → Fin 2) s).toReal *
      weightDifference q s ^ 2) = mixedCount q := by
  have hc : (Fintype.card (Fin n → Fin 2) : ℝ) ≠ 0 := by positivity
  have hw (s : Fin n → Fin 2) : (Foundation.Probability.uniform (Fin n → Fin 2) s).toReal =
      (1 / (Fintype.card (Fin n → Fin 2) : ℝ)) := by
    simp [Foundation.Probability.uniform, PMF.uniformOfFintype_apply]
  simp_rw [hw]
  rw [← Finset.mul_sum, weightDifference_second_moment_exact]
  field_simp

end
end Foundation.Quantum.QKD.PairwiseSampling
