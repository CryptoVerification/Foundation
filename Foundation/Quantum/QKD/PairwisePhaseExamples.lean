import Foundation.Quantum.QKD.PairwisePhaseHash
import Foundation.Quantum.QKD.PairwiseAttackExamples

/-! A concrete coherent attacked-source instantiation and a kernel-checked
phase-support count. This example hashes the full complementary key of the
sampling approximant, not the protocol's remaining final secret key. -/
namespace Foundation.Quantum.QKD.PairwisePhaseExamples
noncomputable section
open PairwisePhaseCoordinates PairwiseAttackExamples
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

def configuration : PairwiseSampling.Configuration 2 := (fun _ => 0, {0})

theorem support_count : acceptedSupport 1 0 1 0 configuration = 1 := by
  simp only [acceptedSupport, phaseSet_band, BB84DelayedDecision.accepts,
    errorCode, Equiv.symm_apply_apply]
  decide

theorem coefficient : bound 1 0 1 0 configuration = 1/4 := by
  norm_num [bound, support_count]

def vector := PairwiseAttackSampling.vector attack (Finset.univ : Finset (Fin 2))

theorem unit : PureProjection.bracket vector vector = 1 := PairwiseAttackSampling.unit _ _

theorem dominated : Subnormalized.Dominated
    (accepted vector unit 1 0 1 0 configuration)
    (reference vector unit 1 0 configuration) (1/4) := by
  rw [← coefficient]
  exact accepted_dominated _ _ _ _ _ _ _

theorem guessing : Subnormalized.probability (accepted vector unit 1 0 1 0 configuration) ≤ 1/4 :=
  Subnormalized.probability_le_dominated _ _ _ dominated

theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin 2) (Fin 1)))
        (fun s => Collision.hashed (accepted vector unit 1 0 1 0 configuration).block (hash s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin 2) (Fin 1)))
        (fun _ => Collision.uniformComparator (Y := Hashing.Bits (Fin 1))
          (accepted vector unit 1 0 1 0 configuration).block)) (1/4) := by
  have hh := hashed_distance (n := 2) (length := 1) vector unit 1 0 1 0 configuration
  convert hh using 1 <;> try rfl
  have hr : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [Hashing.Bits, coefficient, Fintype.card_fun, Fintype.card_fin, ZMod.card, Real.sqrt_div, hr]

end
end Foundation.Quantum.QKD.PairwisePhaseExamples
