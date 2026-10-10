import Foundation.Quantum.QKD.BinaryWeightedVolume
import Foundation.Quantum.QKD.PairwiseReconciledVolume

namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open PairwisePhaseCoordinates BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

/-- Only the population and sample sizes occur in this privacy coefficient. -/
def weightedCoefficient (m tag k gap minKey tolerance : Nat) (t : ℝ) : ℝ :=
  if minKey ≤ m-k then
    (2:ℝ)^(ArbitraryReconciliation.publicBits (m-k)) * Fintype.card (IdealKey.Key tag) *
      ((2:ℝ)^k * (((1+t)^m/t^(supportRadius m k gap tolerance))*(1/2:ℝ)^m))
  else 0

def weightedPrivacyError (m tag length k gap minKey tolerance : Nat) (t : ℝ) : ℝ :=
  (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
    weightedCoefficient m tag k gap minKey tolerance t)

/-- A purely numerical criterion for the already derived physical error. -/
theorem weightedPrivacyError_le (m tag length k gap minKey tolerance : Nat) (t ε : ℝ)
    (hε : 0 ≤ ε)
    (h : Fintype.card (IdealKey.Key length) * weightedCoefficient m tag k gap minKey tolerance t ≤ (2*ε)^2) :
    weightedPrivacyError m tag length k gap minKey tolerance t ≤ ε := by
  have hs := Real.sqrt_le_iff.mpr ⟨by positivity, h⟩
  unfold weightedPrivacyError
  linarith

theorem remainder_count {m : Nat} (c : PairwiseSampling.Configuration m) :
    remainderCount c.2 = m-c.2.card := by
  simp [remainderCount, Fintype.card_subtype_compl, Fintype.card_coe]

theorem complement_card {m : Nat} (c : PairwiseSampling.Configuration m) :
    (Finset.univ \ c.2).card = m-c.2.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem coefficientVolume_le_weighted {m : Nat} (tag k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) (hc : c.2.card = k)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    coefficientVolume tag k gap minKey tolerance c ≤ weightedCoefficient m tag k gap minKey tolerance t := by
  unfold coefficientVolume weightedCoefficient
  rw [complement_card, remainder_count, hc]
  split_ifs
  · unfold volumeBound
    gcongr
    exact BinaryWeightVolume.volume_bound _ _ t ht ht1
  · exact le_rfl

theorem privacyError_le_weighted {m : Nat} (tag length k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration m) (hc : c.2.card = k)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    privacyError tag length k gap minKey tolerance c ≤ weightedPrivacyError m tag length k gap minKey tolerance t := by
  apply (privacyError_le_volume tag length k gap minKey tolerance hk c).trans
  unfold volumePrivacyError weightedPrivacyError
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (coefficientVolume_le_weighted tag k gap minKey tolerance c hc t ht ht1)
    (Nat.cast_nonneg _)

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
