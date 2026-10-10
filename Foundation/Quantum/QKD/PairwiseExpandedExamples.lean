import Foundation.Quantum.QKD.PairwiseExpandedRecovered
import Foundation.Quantum.QKD.PairwiseRecoveredExamples

/-! The coherent two-signal attack with original-position raw keys, the
actual full-position public hash seed, and recovered original attack output. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

def fullBases : Fin 2 → BB84Basis :=
  BB84SiftedInput.joinBases (Finset.univ : Finset (Fin 2)) (PairwiseRecordedSampling.basis configuration, fun _ => .Z)

theorem accepted_expanded :
    OperatorApprox
      (Subnormalized.joint (recoveredExpandedHash (length := 1) PairwiseAttackExamples.attack
        (Finset.univ : Finset (Fin 2)) fullBases 1 0 1 0 configuration))
      (Subnormalized.joint (CommonKey.uniformize (recoveredExpandedHash (length := 1)
        PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2)) fullBases 1 0 1 0 configuration)))
      ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have h := recovered_expanded_secrecy (length := 1) PairwiseAttackExamples.attack
    (Finset.univ : Finset (Fin 2)) fullBases 1 0 1 0 configuration
  convert h using 1
  rw [PairwiseTestExamples.test_count, coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseExpandedExamples
