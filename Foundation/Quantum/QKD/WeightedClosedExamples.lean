import Foundation.Quantum.QKD.WeightedClosed
import Foundation.Quantum.QKD.PairwiseReconciledExamples

/-! Numerical examples for the closed-form envelope. The privacy term keeps
the complete public-disclosure charge, and no finite sum over sifted counts,
subsets or selectors is evaluated. The sampling term of the total error is
still the polynomial gap bound of the earlier stage. -/
namespace Foundation.Quantum.QKD.PairwiseWeightedExamples
noncomputable section
open Foundation.Quantum.QKD.PairwiseReconciledVerification
open Foundation.Quantum.QKD.FullReconciledSecurity
set_option backward.isDefEq.respectTransparency false

set_option exponentiation.threshold 2048 in
/-- The same numerical privacy bound as the exact one, now with the
closed-form envelope. -/
theorem thousand_privacy_closed :
    weightedPrivacyErrorClosed 1000 20 20 100 1000 900 0 (1/16) ≤ (1/2:ℝ)^51 := by
  apply weightedPrivacyErrorClosed_le
  · positivity
  · norm_num [weightedCoefficientClosed, PairwisePhaseCoordinates.supportRadius,
      ArbitraryReconciliation.publicBits, IdealKey.Key, Fintype.card_fun, Fintype.card_fin ]

/-- The whole final output, with the privacy term closed. -/
theorem attacked_full_secure_closed :
    IdealKey.Secure (realState (tag := 1) (length := 1) PairwiseReconciledExamples.attack 1 1 0)
      (1/2 + (2 * Real.sqrt (PairwiseSampling.gapBound 4 1 2) +
        weightedPrivacyErrorClosed 4 1 1 1 2 1 0 (1/16))) :=
  real_secure_closed (tag := 1) (length := 1) PairwiseReconciledExamples.attack 1 2 1 0
    (by decide) (by decide) (1/16) (by norm_num) (by norm_num)

/-- An exact distribution check: the probability of exactly two matches
among four independent basis choices is six sixteenths. -/
theorem four_sifting_two :
    (∑ M : Finset (Fin 4), (Foundation.Probability.uniform (Finset (Fin 4)) M).toReal *
      (if M.card = 2 then (1:ℝ) else 0)) = 3/8 := by
  rw [uniform_sifting_count 4 (fun m => if m = 2 then (1:ℝ) else 0)]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- The closed-form privacy envelope for the four-signal copying attack,
evaluated exactly. The envelope is tight only when the shortest admissible
sifted count is the population size; here it is short, so the value is
larger than the exact one at the largest count. -/
theorem four_signal_privacy_closed :
    weightedPrivacyErrorClosed 4 1 1 1 2 1 0 (1/16) ≤ (25:ℝ) := by
  apply weightedPrivacyErrorClosed_le
  · positivity
  · norm_num [weightedCoefficientClosed, PairwisePhaseCoordinates.supportRadius,
      ArbitraryReconciliation.publicBits, IdealKey.Key, Fintype.card_fun, Fintype.card_fin ]

end
end Foundation.Quantum.QKD.PairwiseWeightedExamples
