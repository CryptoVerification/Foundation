import Foundation.Quantum.QKD.PairwiseVerifiedRecovery
import Foundation.Quantum.QKD.VerifiedHashDistance
import Foundation.Quantum.QKD.PairwisePhaseExamples

/-! Both independent public seeded procedures on the actual recovered joint
raw density of the same nontrivial coherent two-signal attacked certificate. -/
namespace Foundation.Quantum.QKD.PairwiseVerifiedRecoveryExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem recovered_physical : OperatorApprox
    (Subnormalized.joint (VerifiedHash.fromDensity (tag := 1) (length := 1)
      (recoveredRaw PairwiseAttackExamples.attack Finset.univ 1 0 1 0 configuration)))
    (Subnormalized.joint (CommonKey.uniformize (VerifiedHash.fromDensity (tag := 1) (length := 1)
      (recoveredRaw PairwiseAttackExamples.attack Finset.univ 1 0 1 0 configuration)))) (1/2) := by
  have h := recovered_verified_physical_secrecy (tag := 1) (length := 1)
    PairwiseAttackExamples.attack Finset.univ 1 0 1 0 configuration
  convert h using 1
  rw [coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseVerifiedRecoveryExamples
