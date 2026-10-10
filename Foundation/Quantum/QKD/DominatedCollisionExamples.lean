import Foundation.Quantum.QKD.DominatedCollision
import Foundation.Quantum.QKD.LinearHash
import Foundation.Quantum.WeightedObservationExamples

/-! Two private bits and noncommuting single-qubit side information, followed
by a fresh random one-row binary matrix hash. An explicit faithful reference
and a proved domination inequality give an observation error sqrt(1/2)/2. -/
namespace Foundation.Quantum.QKD.DominatedCollisionExamples
noncomputable section
open scoped ComplexOrder
open Collision Hashing
set_option backward.isDefEq.respectTransparency false

abbrev Input := Bits (Fin 2)
abbrev Output := Bits (Fin 1)
abbrev Seeds := Seed (Fin 2) (Fin 1)

def blocks (x : Input) : Operator .bit := (1/4:ℂ) • (prepare (if x 0 = 0 then .Z else .X) 0).matrix

def cq : Guessing.CQ Input .bit where
  block := blocks
  positive x := (prepare _ _).positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by
    simp only [blocks, Matrix.trace_smul, (prepare _ _).normalized, smul_eq_mul, mul_one]
    norm_num [Fintype.card_fun, ZMod.card]

def state : Subnormalized.State Input .bit := Subnormalized.ofCQ cq
abbrev reference : Density .bit := WeightedObservationExamples.mixed

theorem reference_isUnit : IsUnit reference.matrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero]
  norm_num [reference, WeightedObservationExamples.mixed, Matrix.det_fin_two,
    Matrix.smul_apply, Matrix.one_apply]

theorem prepare_complement (θ : BB84Basis) : (1-(prepare θ 0).matrix).PosSemidef := by
  cases θ with
  | Z =>
    have he : (prepare .Z 0).matrix = (basisDensity .bit 0).matrix := by
      simp only [prepare, basisChannel, Channel.identity, Channel.run, Channel.ofIsometry,
        Kraus.single_apply, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [he]
    have hb : (basisDensity .bit 0).matrix = (basisEffect .bit 0).matrix := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [basisDensity, basisEffect, projector]
    rw [hb]
    exact (basisEffect .bit 0).complement_positive
  | X =>
    have h := (measurementEffect .X 0).complement_positive
    rw [WeightedObservationExamples.measurement_matrix] at h
    exact h

theorem domination : Subnormalized.Dominated state reference (1/2) := by
  intro x
  have hp := (prepare_complement (if x 0 = 0 then .Z else .X)).smul
    (by apply Complex.nonneg_iff.mpr; norm_num : (0:ℂ) ≤ 1/4)
  change (((1/2:ℝ):ℂ) • ((1/2:ℂ) • 1) - (1/4:ℂ) • (prepare (if x 0 = 0 then .Z else .X) 0).matrix).PosSemidef
  convert hp using 1; norm_num [smul_sub, smul_smul]

theorem collision_bound (x x' : Input) (hx : x ≠ x') :
    collision (Foundation.Probability.uniform Seeds) linearHash x x' ≤ 1 / Fintype.card Output := by
  have h := linear_collision (O := Fin 1) x x' hx
  simpa only [collision, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat] using le_of_eq h

/-- All private input values, the fresh public hash seed, and the qubit are
actual finite data. The input bound comes from the proved matrix domination. -/
theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform Seeds) (fun s => hashed state.block (linearHash s)))
      (publicMixture (Foundation.Probability.uniform Seeds) (fun _ => uniformComparator (Y := Output) state.block))
      ((1/2:ℝ)*Real.sqrt (1/2)) := by
  have h := dominated_published_distance (Foundation.Probability.uniform Seeds) linearHash
    state reference reference_isUnit (1/2) domination collision_bound
  convert h using 1
  norm_num [state, Subnormalized.mass_ofCQ, Fintype.card_fun, ZMod.card]

theorem error_lt_half : (1/2:ℝ)*Real.sqrt (1/2) < 1/2 := by
  have h := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  rw [Real.sqrt_one] at h
  nlinarith

theorem blocks_zero_entry (i j : Fin 2) : blocks (0:Input) i j = if i = 0 ∧ j = 0 then 1/4 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [blocks, prepare, basisChannel, Channel.run, Channel.ofIsometry,
      Channel.identity, Kraus.single_apply, basisDensity, Matrix.diagonal_apply]

theorem blocks_one_entry (i j : Fin 2) : blocks (1:Input) i j = 1/8 := by
  simp only [blocks, Pi.one_apply, show ¬(1:ZMod 2) = 0 by decide, ite_false,
    Matrix.smul_apply, smul_eq_mul, prepare_plus_matrix]
  norm_num

theorem blocks_noncommute : blocks (0:Input) * blocks (1:Input) ≠ blocks (1:Input) * blocks (0:Input) := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, blocks_zero_entry, blocks_one_entry] at hh

end
end Foundation.Quantum.QKD.DominatedCollisionExamples
