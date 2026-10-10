import Foundation.Quantum.QKD.SiftingCountAverage
import Foundation.Quantum.QKD.PairwiseReconciledExamples

namespace Foundation.Quantum.QKD.PairwiseWeightedExamples
noncomputable section
open PairwiseReconciledVerification FullReconciledSecurity
set_option backward.isDefEq.respectTransparency false

/-- Twenty output bits; the complete public disclosure charge is included.
This numerical example concerns PA only, not the total sampling error. -/
set_option exponentiation.threshold 2048 in
theorem thousand_privacy_bound :
    weightedPrivacyError 1000 20 20 100 1000 900 0 (1/16) ≤ (1/2:ℝ)^51 := by
  apply weightedPrivacyError_le
  · positivity
  · norm_num [weightedCoefficient, PairwisePhaseCoordinates.supportRadius,
      ArbitraryReconciliation.publicBits, IdealKey.Key, Fintype.card_fun, Fintype.card_fin ]

theorem actual_thousand_privacy (c : PairwiseSampling.Configuration 1000) (hc : c.2.card = 100) :
    privacyError 20 20 100 1000 900 0 c ≤ (1/2:ℝ)^51 :=
  (privacyError_le_weighted 20 20 100 1000 900 0 (by decide) c hc (1/16) (by norm_num) (by norm_num)).trans
    thousand_privacy_bound

/-- An exact distribution check: the probability of exactly two matches
among four independent basis choices is six sixteenths. -/
theorem four_sifting_two :
    (∑ M : Finset (Fin 4), (Foundation.Probability.uniform (Finset (Fin 4)) M).toReal *
      (if M.card = 2 then (1:ℝ) else 0)) = 3/8 := by
  rw [uniform_sifting_count 4 (fun m => if m = 2 then (1:ℝ) else 0)]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- The same physical copying attack, with no phase-support or test-set
average remaining in the stated upper bound. -/
theorem attacked_full_secure :
    IdealKey.Secure (realState (tag := 1) (length := 1) PairwiseReconciledExamples.attack 1 1 0)
      (1/2 + (2 * Real.sqrt (PairwiseSampling.gapBound 4 1 2) +
        countWeightedError 4 1 1 1 2 1 0 (1/16))) := by
  have h := real_secure_count (tag := 1) (length := 1)
    PairwiseReconciledExamples.attack 1 2 1 0 (by decide) (by decide) (1/16) (by norm_num) (by norm_num)
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseWeightedExamples
