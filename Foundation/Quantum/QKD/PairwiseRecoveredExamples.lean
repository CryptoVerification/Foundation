import Foundation.Quantum.QKD.PairwiseRecoveredSecrecy
import Foundation.Quantum.QKD.PairwisePublicExamples

/-! The same coherent attack, with the extra purification label physically
removed and its original quantum output retained in the secrecy comparison. -/
namespace Foundation.Quantum.QKD.PairwiseRecoveredExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem accepted_recovered :
    OperatorApprox
      (Subnormalized.joint (recoveredAcceptedHash (length := 1) PairwiseAttackExamples.attack
        (Finset.univ : Finset (Fin 2)) 1 0 1 0 configuration))
      (Subnormalized.joint (CommonKey.uniformize (recoveredAcceptedHash (length := 1)
        PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2)) 1 0 1 0 configuration)))
      ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have h := recovered_accepted_secrecy (length := 1) PairwiseAttackExamples.attack
    (Finset.univ : Finset (Fin 2)) 1 0 1 0 configuration
  convert h using 1
  rw [PairwiseTestExamples.test_count, coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseRecoveredExamples
