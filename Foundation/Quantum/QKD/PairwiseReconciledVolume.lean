import Foundation.Quantum.QKD.PairwiseSupportVolume
import Foundation.Quantum.QKD.PairwiseReconciledPrivacy

/-! A binomial-volume bound on the same physical privacy amplification error,
charging syndrome, copied suffix, tested bits and verification tag. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

def coefficientVolume {m : Nat} (tag k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) : ℝ :=
  if minKey ≤ (Finset.univ \ c.2).card then
    (2:ℝ)^(ArbitraryReconciliation.publicBits (BB84SiftedInput.remainderCount c.2)) *
      Fintype.card (IdealKey.Key tag) * ((2:ℝ)^c.2.card * volumeBound m k gap tolerance)
  else 0

theorem coefficient_le_volume {m : Nat} (tag k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration m) :
    coefficient tag k gap minKey tolerance c ≤ coefficientVolume tag k gap minKey tolerance c := by
  unfold coefficientVolume
  split_ifs with h
  · rw [coefficient_public_bits]
    gcongr
    exact bound_le_volume k gap minKey tolerance hk c
  · simp [coefficient, bound, acceptedSupport_zero_short k gap minKey tolerance c h]

def volumePrivacyError {m : Nat} (tag length k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) : ℝ :=
  (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
    coefficientVolume tag k gap minKey tolerance c)

theorem privacyError_le_volume {m : Nat} (tag length k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration m) :
    privacyError tag length k gap minKey tolerance c ≤ volumePrivacyError tag length k gap minKey tolerance c := by
  have hc := coefficient_nonneg tag k gap minKey tolerance c
  have hd : 0 ≤ 1 / (Fintype.card (IdealKey.Key length) : ℝ) := by positivity
  have h : (1-1/(Fintype.card (IdealKey.Key length) : ℝ)) *
      (coefficient tag k gap minKey tolerance c * 1) ≤ coefficient tag k gap minKey tolerance c := by
    nlinarith
  unfold privacyError volumePrivacyError
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (h.trans (coefficient_le_volume tag k gap minKey tolerance hk c))
    (Nat.cast_nonneg _)

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
