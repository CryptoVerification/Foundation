import Foundation.Quantum.QKD.PairwiseRealSecrecy
import Foundation.Quantum.QKD.PairwiseGlobalExamples

/-! The actual whole randomized coherent attack, not just its sampling
approximant. The error includes both proved sampling and privacy contributions. -/
namespace Foundation.Quantum.QKD.PairwiseRealExamples
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

theorem attacked_real :
    OperatorApprox
      (Subnormalized.joint (realAcceptedHash (length := 1) PairwiseAttackExamples.attack 1 1 0))
      (Subnormalized.joint (CommonKey.uniformize
        (realAcceptedHash (length := 1) PairwiseAttackExamples.attack 1 1 0)))
      (2*PairwiseRandomizedSampling.error 2 1 1 + privacyError 2 1 1 1 1 0) :=
  real_accepted_secrecy _ _ _ _ _

end
end Foundation.Quantum.QKD.PairwiseRealExamples
