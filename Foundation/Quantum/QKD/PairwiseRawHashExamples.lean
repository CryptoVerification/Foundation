import Foundation.Quantum.QKD.PairwiseRawHashPrivacy

namespace Foundation.Quantum.QKD.PairwiseRawHashExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

/-- Same nontrivial attacked approximant and actual position-labelled hash.
The real-to-approximant sampling error has not been added to this statement. -/
theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1))
        (fun s => Collision.hashed (testedKey vector unit 1 0 1 0 configuration).block
          (remainingHash configuration.2 s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key 1)
          (testedKey vector unit 1 0 1 0 configuration).block)) ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have hh := rawHashPrivacy (n := 2) (length := 1) vector unit 1 0 1 0 configuration
  convert hh using 1 <;> try rfl
  rw [PairwiseTestExamples.test_count, coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseRawHashExamples
