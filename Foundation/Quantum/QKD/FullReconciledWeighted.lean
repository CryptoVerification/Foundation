import Foundation.Quantum.QKD.PairwiseWeightedPrivacy
import Foundation.Quantum.QKD.FullReconciledVolume

/-! Fixed-size test support removes the selector and test averages from the
privacy error. The original random sifting-set distribution is retained. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open BB84SiftedInput PairwiseReconciledVerification
set_option backward.isDefEq.respectTransparency false

theorem configuration_zero_of_card_ne {m : Nat} (k : Nat) (hk : k ≤ m)
    (c : PairwiseSampling.Configuration m) (hc : c.2.card ≠ k) :
    PairwiseSampling.distribution m k hk c = 0 := by
  apply PMF.uniformOfFinset_apply_of_notMem
  simp [PairwiseSampling.configurations, hc]

/-- This expression contains neither selectors nor test-position sets. -/
def conditionalWeightedError {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (t : ℝ) : ℝ :=
  if k ≤ selectedCount M then
    weightedPrivacyError (selectedCount M) tag length k gap minKey tolerance t
  else 0

def globalWeightedError (n tag length k gap minKey tolerance : Nat) (t : ℝ) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
    conditionalWeightedError tag length M k gap minKey tolerance t

theorem conditional_privacy_le_weighted {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    conditionalSecrecyError tag length M k gap minKey tolerance ≤
      conditionalWeightedError tag length M k gap minKey tolerance t := by
  unfold conditionalSecrecyError conditionalWeightedError
  split_ifs with hk
  · have hlen : BB84SiftingRandomness.requiredLength M k minKey = minKey := by
      simp only [BB84SiftingRandomness.requiredLength]
      rw [if_pos (by simpa only [selectedCount, Fintype.card_coe] using hk)]
    unfold conditionalPrivacyError
    rw [hlen]
    calc
      _ ≤ ∑ c : PairwiseSampling.Configuration (selectedCount M),
          (PairwiseSampling.distribution (selectedCount M) k hk c).toReal *
          weightedPrivacyError (selectedCount M) tag length k gap minKey tolerance t := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : c.2.card = k
        · exact mul_le_mul_of_nonneg_left
            (privacyError_le_weighted tag length k gap minKey tolerance hk0 c hc t ht ht1) ENNReal.toReal_nonneg
        · rw [configuration_zero_of_card_ne k hk c hc]
          simp
      _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]
  · exact le_rfl

theorem global_privacy_le_weighted (n tag length k gap minKey tolerance : Nat)
    (hk0 : 0 < k) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    globalPrivacyError n tag length k gap minKey tolerance ≤
      globalWeightedError n tag length k gap minKey tolerance t := by
  unfold globalPrivacyError globalWeightedError
  apply Finset.sum_le_sum
  intro M _
  exact mul_le_mul_of_nonneg_left
    (conditional_privacy_le_weighted tag length M k gap minKey tolerance hk0 t ht ht1) ENNReal.toReal_nonneg

theorem real_secure_weighted {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (hg : 0 < gap)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*Real.sqrt (PairwiseSampling.gapBound n k gap) +
          globalWeightedError n tag length k gap minKey tolerance t)) := by
  have h := real_secure_gap (tag := tag) (length := length) A k gap minKey tolerance hk0 hg
  have he := global_privacy_le_weighted n tag length k gap minKey tolerance hk0 t ht ht1
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
