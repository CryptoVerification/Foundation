import Foundation.Quantum.QKD.PairwiseConditionalSecrecy
import Foundation.Quantum.QKD.PairwiseExpandedExamples

/-! Accepted secrecy of the same coherent attacked approximant after full
position restoration and physical removal of unmatched quantum signals. -/
namespace Foundation.Quantum.QKD.PairwiseFinishedExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem accepted_finished :
    OperatorApprox
      (Subnormalized.joint (finishedAcceptedHash (length := 1) PairwiseAttackExamples.attack
        (Finset.univ : Finset (Fin 2)) PairwiseExpandedExamples.fullBases 1 0 1 0 configuration))
      (Subnormalized.joint (CommonKey.uniformize (finishedAcceptedHash (length := 1)
        PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2)) PairwiseExpandedExamples.fullBases
        1 0 1 0 configuration)))
      ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have h := finished_accepted_secrecy (length := 1) PairwiseAttackExamples.attack
    (Finset.univ : Finset (Fin 2)) PairwiseExpandedExamples.fullBases 1 0 1 0 configuration
  convert h using 1
  rw [PairwiseTestExamples.test_count, coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseFinishedExamples
