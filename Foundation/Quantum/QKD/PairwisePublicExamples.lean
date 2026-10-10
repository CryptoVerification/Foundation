import Foundation.Quantum.QKD.PairwiseAcceptedHash

/-! Accepted-branch secrecy for the actual reconstructed raw record of the
same nontrivial attacked approximant, with original public transcript and seed.
The real-state sampling error and whole-protocol correctness remain separate. -/
namespace Foundation.Quantum.QKD.PairwisePublicExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem accepted_interpreted :
    OperatorApprox (Subnormalized.joint (acceptedRawHash (length := 1) vector unit 1 0 1 0 configuration))
      (Subnormalized.joint (CommonKey.uniformize (acceptedRawHash (length := 1) vector unit 1 0 1 0 configuration)))
      ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have h := accepted_raw_secrecy (n := 2) (length := 1) vector unit 1 0 1 0 configuration
  convert h using 1 <;> try rfl
  rw [PairwiseTestExamples.test_count, coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwisePublicExamples
