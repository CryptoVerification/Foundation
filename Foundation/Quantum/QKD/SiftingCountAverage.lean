import Foundation.Quantum.QKD.FullReconciledWeighted
import Mathlib.Data.Nat.Choose.Sum

/-! The uniform sifting-set average is exactly a binomial average over its
size. This is a distribution identity, independent of any quantum attack. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem uniform_sifting_count (n : Nat) (f : Nat → ℝ) :
    (∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal * f M.card) =
      ∑ m ∈ Finset.range (n+1), ((Nat.choose n m : ℝ)/(2:ℝ)^n) * f m := by
  have h := Finset.sum_powerset_apply_card f (x := (Finset.univ : Finset (Fin n)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simp only [Foundation.Probability.uniform, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- A one-dimensional finite sum, with all insufficient and short branches
still zero. No subset, selector or binary pattern is enumerated. -/
def countWeightedError (n tag length k gap minKey tolerance : Nat) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n+1), ((Nat.choose n m : ℝ)/(2:ℝ)^n) *
    (if k ≤ m then PairwiseReconciledVerification.weightedPrivacyError m tag length k gap minKey tolerance t else 0)

theorem globalWeightedError_count (n tag length k gap minKey tolerance : Nat) (t : ℝ) :
    globalWeightedError n tag length k gap minKey tolerance t =
      countWeightedError n tag length k gap minKey tolerance t := by
  unfold globalWeightedError conditionalWeightedError countWeightedError
  simp only [BB84SiftedInput.selectedCount, Fintype.card_coe]
  exact uniform_sifting_count n (fun m => if k ≤ m then
    PairwiseReconciledVerification.weightedPrivacyError m tag length k gap minKey tolerance t else 0)

theorem real_secure_count {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (hg : 0 < gap)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*Real.sqrt (PairwiseSampling.gapBound n k gap) +
          countWeightedError n tag length k gap minKey tolerance t)) := by
  simpa only [globalWeightedError_count] using
    real_secure_weighted (tag := tag) (length := length) A k gap minKey tolerance hk0 hg t ht ht1

end
end Foundation.Quantum.QKD.FullReconciledSecurity
