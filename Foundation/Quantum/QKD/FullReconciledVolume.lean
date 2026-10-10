import Foundation.Quantum.QKD.PairwiseReconciledVolume
import Foundation.Quantum.QKD.PairwiseAnalyticSecurity

/-! Replace exact phase-support enumeration in the full physical BB84 bound
by binomial volumes, preserving every public record and abort branch. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

def conditionalVolumeError {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) : ℝ :=
  if hk : k ≤ selectedCount M then
    ∑ c, (PairwiseSampling.distribution (selectedCount M) k hk c).toReal *
      PairwiseReconciledVerification.volumePrivacyError tag length k gap
        (BB84SiftingRandomness.requiredLength M k minKey) tolerance c
  else 0

def globalVolumeError (n tag length k gap minKey tolerance : Nat) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
    conditionalVolumeError tag length M k gap minKey tolerance

theorem conditional_privacy_le_volume {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) :
    conditionalSecrecyError tag length M k gap minKey tolerance ≤
      conditionalVolumeError tag length M k gap minKey tolerance := by
  unfold conditionalSecrecyError conditionalVolumeError
  split_ifs with hk
  · unfold conditionalPrivacyError
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_left
      (PairwiseReconciledVerification.privacyError_le_volume _ _ _ _ _ _ hk0 c) ENNReal.toReal_nonneg
  · exact le_rfl

theorem global_privacy_le_volume (n tag length k gap minKey tolerance : Nat) (hk0 : 0 < k) :
    globalPrivacyError n tag length k gap minKey tolerance ≤
      globalVolumeError n tag length k gap minKey tolerance := by
  unfold globalPrivacyError globalVolumeError
  apply Finset.sum_le_sum
  intro M _
  exact mul_le_mul_of_nonneg_left
    (conditional_privacy_le_volume tag length M k gap minKey tolerance hk0) ENNReal.toReal_nonneg

/-- The real two-key output includes reconciliation, verification, privacy
amplification, the adversary register and all accepted and aborted records. -/
theorem real_secure_volume {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (hg : 0 < gap) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*Real.sqrt (PairwiseSampling.gapBound n k gap) + globalVolumeError n tag length k gap minKey tolerance)) := by
  have h := real_secure_gap (tag := tag) (length := length) A k gap minKey tolerance hk0 hg
  have he := global_privacy_le_volume n tag length k gap minKey tolerance hk0
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
