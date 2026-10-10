import Foundation.Quantum.QKD.PairwiseAlicePrivacy
import Foundation.Quantum.QKD.PairwiseAlicePhysical
import Foundation.Quantum.QKD.PairwisePhaseExamples

/-! Alice-coordinate privacy on the same nontrivial attacked approximant.
The test positions are still included; this is not final BB84 secrecy. -/
namespace Foundation.Quantum.QKD.PairwiseAliceExamples
noncomputable section
open PairwisePhaseCoordinates PairwisePhaseExamples
set_option backward.isDefEq.respectTransparency false

theorem dominated : Subnormalized.Dominated
    (acceptedAlice vector unit 1 0 1 0 configuration)
    (reference vector unit 1 0 configuration) (1/4) := by
  rw [← coefficient]
  exact acceptedAlice_dominated _ _ _ _ _ _ _

theorem guessing : Subnormalized.probability (acceptedAlice vector unit 1 0 1 0 configuration) ≤ 1/4 :=
  Subnormalized.probability_le_dominated _ _ _ dominated

theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin 2) (Fin 1)))
        (fun s => Collision.hashed (acceptedAlice vector unit 1 0 1 0 configuration).block (hash s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin 2) (Fin 1)))
        (fun _ => Collision.uniformComparator (Y := Hashing.Bits (Fin 1))
          (acceptedAlice vector unit 1 0 1 0 configuration).block)) (1/4) := by
  have hh := alicePrivacy (n := 2) vector unit 1 0 1 0 configuration
    (Foundation.Probability.uniform (Hashing.Seed (Fin 2) (Fin 1))) hash collision
  change OperatorApprox _ _ _ at hh
  convert hh using 1 <;> try rfl
  have hr : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [Hashing.Bits, coefficient, Fintype.card_fun, Fintype.card_fin, ZMod.card, Real.sqrt_div, hr]

end
end Foundation.Quantum.QKD.PairwiseAliceExamples
