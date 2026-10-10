import Foundation.Quantum.QKD.PairwiseDeviationQuantum
import Foundation.Quantum.QKD.FullReconciledSecurity

/-! The separated bound propagates to the existing complete reconciled BB84
experiment, including both keys and aborts. The residual sampling maximum is
still exact finite data, not an assumed concentration theorem. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem errorBound_separated (n k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    (errorBound n k gap).toReal ≤ separatedBound n k hk u t := by
  obtain ⟨q,_,hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Pattern n))
    Finset.univ_nonempty (badCount n k gap)
  have he : Foundation.Probability.eventProb (distribution n k hk) (bad k gap q) = errorBound n k gap := by
    rw [probability_count]
    unfold errorBound maxBadCount
    rw [hq]
  have h := classical_separated n k gap hk u t ht hgap q
  rwa [he] at h

end
end Foundation.Quantum.QKD.PairwiseSampling

namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

/-- Same selected-set weights and insufficient-test zero branches. -/
def separatedSamplingError (n k : Nat) (u t : ℝ) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
    (if hk : k ≤ selectedCount M then Real.sqrt (PairwiseSampling.separatedBound (selectedCount M) k hk u t) else 0)

theorem sampling_error_separated (n k gap : Nat) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    PairwiseRandomizedSampling.error n k gap ≤ separatedSamplingError n k u t := by
  unfold PairwiseRandomizedSampling.error separatedSamplingError
  apply Finset.sum_le_sum
  intro M _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  unfold PairwiseRandomizedSampling.conditionalError
  split_ifs with hk
  · exact Real.sqrt_le_sqrt (PairwiseSampling.errorBound_separated (selectedCount M) k gap hk u t ht hgap)
  · rfl

/-- The actual complete protocol and idealization are unchanged. This is an
alternative proved error expression, not yet a small numerical error claim. -/
theorem real_secure_separated {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (u t : ℝ) (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*separatedSamplingError n k u t + globalPrivacyError n tag length k gap minKey tolerance)) := by
  have h := real_verified_secure (tag := tag) (length := length) A k gap minKey tolerance
  have he := sampling_error_separated n k gap u t ht hgap
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
