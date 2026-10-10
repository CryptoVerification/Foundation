import Foundation.Quantum.QKD.PairwiseVerificationRaw
import Foundation.Quantum.QKD.PairwisePhaseExamples

/-! The same nontrivial two-signal coherent joint attack, now with the actual
two-key check and its public one-bit tag. This is a support-state result;
real-to-support error and full finalization have not been added. -/
namespace Foundation.Quantum.QKD.PairwiseVerificationExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem dominated (s : Hashing.RawSeed 2 1) : Subnormalized.Dominated
    (verifiedTagKey (n := 2) vector unit 1 0 1 0 configuration s)
    (Subnormalized.leakedReference (C := IdealKey.Key 1)
      (Subnormalized.leakedReference
        (C := (qubits (BB84SiftedInput.selectedCount configuration.2)).Basis)
        (reference (n := 2) vector unit 1 0 configuration))) 1 := by
  have h := verified_tag_dominated (n := 2) vector unit 1 0 1 0 configuration s
  convert h using 1
  rw [coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

theorem interpreted : OperatorApprox
    (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) (fun s =>
      publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1))
        (fun r => Collision.hashed (verifiedTagKey (n := 2) vector unit 1 0 1 0 configuration s).block
          (remainingHash (n := 2) configuration.2 r))))
    (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) (fun s =>
      publicMixture (Foundation.Probability.uniform (Hashing.RawSeed 2 1))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key 1)
          (verifiedTagKey (n := 2) vector unit 1 0 1 0 configuration s).block))) (1/2) := by
  have h := verified_hash_average (n := 2) (tag := 1) (length := 1) vector unit 1 0 1 0 configuration
  convert h using 1
  rw [coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseVerificationExamples
