import Foundation.Quantum.QKD.PairwiseTestPrivacy
import Foundation.Quantum.QKD.PairwiseAliceExamples

/-! One retained bit and one disclosed test bit, on the same two-signal
coherently attacked sampling approximant. No real-protocol secrecy claim. -/
namespace Foundation.Quantum.QKD.PairwiseTestExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem test_count : configuration.2.card = 1 := by decide

theorem dominated : Subnormalized.Dominated
    (testedKey vector unit 1 0 1 0 configuration)
    (Subnormalized.leakedReference
      (C := (qubits (BB84SiftedInput.selectedCount configuration.2)).Basis)
      (reference vector unit 1 0 configuration)) (1/2) := by
  have hh := tested_dominated vector unit 1 0 1 0 configuration
  convert hh using 1
  rw [test_count, coefficient]
  norm_num

theorem guessing : Subnormalized.probability (testedKey vector unit 1 0 1 0 configuration) ≤ 1/2 :=
  Subnormalized.probability_le_dominated _ _ _ dominated

theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform
          (Hashing.Seed (Fin (BB84SiftedInput.remainderCount configuration.2)) (Fin 1)))
        (fun s => Collision.hashed (testedKey vector unit 1 0 1 0 configuration).block (hash s)))
      (publicMixture (Foundation.Probability.uniform
          (Hashing.Seed (Fin (BB84SiftedInput.remainderCount configuration.2)) (Fin 1)))
        (fun _ => Collision.uniformComparator (Y := Hashing.Bits (Fin 1))
          (testedKey vector unit 1 0 1 0 configuration).block)) ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have hh := testedPrivacy vector unit 1 0 1 0 configuration
    (Foundation.Probability.uniform
      (Hashing.Seed (Fin (BB84SiftedInput.remainderCount configuration.2)) (Fin 1))) hash collision
  change OperatorApprox _ _ _ at hh
  convert hh using 1
  rw [test_count, coefficient]
  norm_num [Hashing.Bits, Fintype.card_fun, Fintype.card_fin, ZMod.card]

end
end Foundation.Quantum.QKD.PairwiseTestExamples
