import Foundation.Quantum.QKD.PairwiseVerificationPublicRaw
import Foundation.Quantum.QKD.PairwiseVerificationExamples

/-! The same coherent joint attack, checked and hashed directly at its raw
output, with the original transcript, tag and both public seeds retained. -/
namespace Foundation.Quantum.QKD.PairwiseVerificationPublicExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem direct_raw (s : Hashing.RawSeed 2 1) : OperatorApprox
    (Subnormalized.joint (verifiedRawHash (n := 2) (length := 1) vector unit 1 0 1 0 configuration s))
    (Subnormalized.joint (CommonKey.uniformize
      (verifiedRawHash (n := 2) (length := 1) vector unit 1 0 1 0 configuration s))) (1/2) := by
  have h := verified_raw_secrecy (n := 2) (length := 1) vector unit 1 0 1 0 configuration s
  convert h using 1
  rw [coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

theorem averaged_raw : OperatorApprox
    (Subnormalized.joint (verifiedRawAverage (n := 2) (tag := 1) (length := 1) vector unit 1 0 1 0 configuration))
    (Subnormalized.joint (CommonKey.uniformize
      (verifiedRawAverage (n := 2) (tag := 1) (length := 1) vector unit 1 0 1 0 configuration))) (1/2) := by
  have h := verified_raw_average_secrecy (n := 2) (tag := 1) (length := 1)
    vector unit 1 0 1 0 configuration
  convert h using 1
  rw [coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseVerificationPublicExamples
