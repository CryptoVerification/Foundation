import Foundation.Quantum.QKD.PairwiseVerifiedSecurity
import Foundation.Quantum.QKD.PairwiseAttackExamples

/-! Whole actual randomized BB84 under the coherent copying attack. The
8-bit check gives a numerical mismatch bound, not a useful secret-key rate:
its disclosure cost is included in the separate full secrecy expression. -/
namespace Foundation.Quantum.QKD.PairwiseVerifiedSecurityExamples
noncomputable section
open PairwiseExpandedVerification
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem attacked_correctness :
    CommonKey.correctnessError (VerifiedHash.bothAverage (tag := 8) (length := 1)
      (Subnormalized.readDensity (Randomized.keyState PairwiseAttackExamples.attack 1 1 0))) ≤ 1/256 := by
  have h := VerifiedHash.bothAverage_correctness (tag := 8) (length := 1)
    (Subnormalized.readDensity (Randomized.keyState PairwiseAttackExamples.attack 1 1 0))
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin] at h ⊢
  exact h

theorem attacked_full_output :
    IdealKey.Secure (realVerifiedState (tag := 8) (length := 1) PairwiseAttackExamples.attack 1 1 0)
      (1/256 + (2*PairwiseRandomizedSampling.error 2 1 1 + globalPrivacyError 2 8 1 1 1 1 0)) := by
  have h := real_verified_secure (tag := 8) (length := 1) PairwiseAttackExamples.attack 1 1 1 0
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin] at h ⊢
  exact h

end
end Foundation.Quantum.QKD.PairwiseVerifiedSecurityExamples
