import Foundation.Quantum.QKD.BB84Measurement
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! BB84's two complementary bases, actual normalized preparation, and
measurement. The real Hadamard gate is additional protocol syntax, distinct
from the square-root-of-X gate used by the original categorical example. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive BB84Basis where
  | Z | X
  deriving DecidableEq, Fintype

def hadamardCoefficient : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

@[simp] theorem hadamardCoefficient_star : star hadamardCoefficient = hadamardCoefficient := by
  simp [hadamardCoefficient]

theorem hadamardCoefficient_square : hadamardCoefficient * hadamardCoefficient = 1 / 2 := by
  have h : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = 1 / 2 :=
    Real.mul_self_sqrt (by norm_num)
  unfold hadamardCoefficient
  rw [← Complex.ofReal_mul, h]
  norm_num

def hadamard : Op .bit .bit := fun i j =>
  if i = 1 ∧ j = 1 then -hadamardCoefficient else hadamardCoefficient

@[simp] theorem hadamard_adjoint : hadamard.conjTranspose = hadamard := by
  ext i j
  change star (if j = 1 ∧ i = 1 then -hadamardCoefficient else hadamardCoefficient) = _
  simp only [hadamard, and_comm]
  split_ifs <;> simp [hadamardCoefficient]

theorem hadamard_square : hadamard * hadamard = (1 : Operator .bit) := by
  ext i j
  change (∑ k : Fin 2, hadamard i k * hadamard k j) = if i = j then 1 else 0
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [hadamard, hadamardCoefficient_square]

def basisChannel : BB84Basis → Channel .bit .bit
  | .Z => Channel.identity .bit
  | .X => Channel.ofIsometry hadamard (by rw [hadamard_adjoint, hadamard_square])

def prepare (θ : BB84Basis) (b : Fin 2) : Density .bit :=
  (basisChannel θ).run (basisDensity .bit b)

def measurementEffect (θ : BB84Basis) (b : Fin 2) : Effect .bit :=
  (basisChannel θ).pullEffect (basisEffect .bit b)

/-- When the bases agree, decoding undoes preparation as an actual state operation. -/
theorem matched_basis_matrix (θ : BB84Basis) (b : Fin 2) :
    ((basisChannel θ).run (prepare θ b)).matrix = (basisDensity .bit b).matrix := by
  cases θ with
  | Z => simp [prepare, basisChannel, Channel.run, Channel.identity, Channel.ofIsometry]
  | X =>
    simp only [prepare, basisChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply]
    rw [hadamard_adjoint]
    calc
      _ = (hadamard * hadamard) * (basisDensity .bit b).matrix *
          (hadamard * hadamard) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hadamard_square, Matrix.one_mul, Matrix.mul_one]

/-- In the absence of attack and noise, the matched-basis outcome is the transmitted bit. -/
theorem matched_basis_correct (θ : BB84Basis) (b : Fin 2) :
    (measurementEffect θ b).probability (prepare θ b) = 1 := by
  rw [measurementEffect, ← Effect.probability_run]
  rw [BB84Attack.basisEffect_probability]
  rw [matched_basis_matrix]
  simp [basisDensity]

end
end Foundation.Quantum.QKD
