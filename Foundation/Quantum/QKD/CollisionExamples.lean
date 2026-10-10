import Foundation.Quantum.QKD.CollisionLogic
import Foundation.Quantum.QKD.BB84Complementary

/-! Noncommuting quantum blocks for a concrete two-universal hash. The input
collision is 1/2, the total marginal purity 3/4, and the centered output collision
1/4. The two conditional quantum states cannot be replaced by scalar weights. -/
namespace Foundation.Quantum.QKD.CollisionExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic
open Collision
set_option backward.isDefEq.respectTransparency false

/-- Uniform private bit, whose two conditional states are Z0 and X0. -/
def blocks (x : Fin 2) : Operator .bit := (1/2:ℂ) • (prepare (if x = 0 then .Z else .X) 0).matrix

theorem blocks_positive (x : Fin 2) : (blocks x).PosSemidef :=
  (prepare _ _).positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)

def state : Guessing.CQ (Fin 2) .bit where
  block := blocks
  positive := blocks_positive
  normalized := by norm_num [blocks, Matrix.trace_smul, (prepare _ _).normalized, Fin.sum_univ_two]

/-- A one-bit uniform seed selects the constant-zero map or the identity. -/
def hash (s x : Fin 2) : Fin 2 := if s = 0 then 0 else x

def seeds : PMF (Fin 2) := Foundation.Probability.uniform (Fin 2)

theorem seed_weight (s : Fin 2) : (seeds s).toReal = 1/2 := by
  norm_num [seeds, Foundation.Probability.uniform, PMF.uniformOfFintype_apply]

theorem hash_collision (x x' : Fin 2) (h : x ≠ x') : collision seeds hash x x' = 1/2 := by
  rw [collision, eventProb_toReal]
  norm_num [hash, Fin.sum_univ_two, seed_weight, h]

theorem blocks_zero (i j : Fin 2) : blocks 0 i j = if i = 0 ∧ j = 0 then 1/2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [blocks, prepare, basisChannel, Channel.run, Channel.ofIsometry,
      Channel.identity, Kraus.single_apply, basisDensity, Matrix.diagonal_apply]

theorem blocks_one (i j : Fin 2) : blocks 1 i j = 1/4 := by
  simp only [blocks, show ¬ (1:Fin 2) = 0 by decide, ite_false,
    Matrix.smul_apply, smul_eq_mul, prepare_plus_matrix]
  norm_num

/-- The quantum cross term differs from the product of the classical weights. -/
theorem cross_pair : pair blocks 0 1 = 1/8 := by
  norm_num [pair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    blocks_zero, blocks_one]

theorem blocks_noncommute : blocks 0 * blocks 1 ≠ blocks 1 * blocks 0 := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, blocks_zero, blocks_one] at hh

theorem input_value : input blocks = 1/2 := by
  norm_num [input, pair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    blocks_zero, blocks_one]

theorem total_value : total blocks = 3/4 := by
  rw [total_expansion]
  norm_num [pair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    blocks_zero, blocks_one]

theorem output_value : output seeds hash blocks = 5/8 := by
  rw [output_expansion]
  have hc : collision seeds hash 0 1 = 1/2 := hash_collision _ _ (by decide)
  have hc' : collision seeds hash 1 0 = 1/2 := hash_collision _ _ (by decide)
  norm_num [Fin.sum_univ_two, collision_self, hc, hc', pair, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, blocks_zero, blocks_one]

theorem variance_value : variance seeds hash blocks = 1/4 := by
  rw [variance_expansion, output_value, total_value]
  norm_num

def proof : Derivation (CollisionLogic.presentation 2) (Logic.Context.singleton (.input 0 (1/2)))
    (.variance 0 (1/4)) := CollisionLogic.proof 2 0 (1/2) (1/4) (by norm_num)

theorem interpreted : variance seeds hash blocks ≤ 1/4 := by
  apply CollisionLogic.sound seeds hash (fun _ => blocks) (fun _ => blocks_positive)
    (fun x x' hx => by simpa only [Fintype.card_fin, Nat.cast_ofNat] using le_of_eq (hash_collision x x' hx)) proof
  intro _
  exact le_of_eq input_value

end
end Foundation.Quantum.QKD.CollisionExamples
