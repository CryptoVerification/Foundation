import Foundation.Quantum.States
import Mathlib.Analysis.Matrix.Order

/-! Binary measurements and the Heisenberg action of a physical channel. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

structure Effect (a : Space) where
  matrix : Operator a
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

namespace Kraus
variable {a b : Space}

def dual (K : Kraus a b) (E : Operator b) : Operator a :=
  ∑ k, (K.operator k).conjTranspose * E * K.operator k

theorem dual_positive (K : Kraus a b) {E : Operator b} (h : E.PosSemidef) :
    (K.dual E).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => h.conjTranspose_mul_mul_same _)

theorem trace_dual (K : Kraus a b) (ρ : Operator a) (E : Operator b) :
    (E * K.apply ρ).trace = (K.dual E * ρ).trace := by
  simp only [apply, dual, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  congr 1
  funext k
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

@[simp] theorem dual_one (K : Kraus a b) : K.dual 1 = K.effect := by
  simp [dual, effect]

theorem dual_sub (K : Kraus a b) (E F : Operator b) :
    K.dual (E - F) = K.dual E - K.dual F := by
  simp [dual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
end Kraus

namespace Channel
variable {a b : Space}

def pullEffect (C : Channel a b) (E : Effect b) : Effect a where
  matrix := C.toKraus.dual E.matrix
  positive := C.toKraus.dual_positive E.positive
  complement_positive := by
    have h := C.toKraus.dual_positive E.complement_positive
    simpa [Kraus.dual_sub, C.complete] using h
end Channel

open scoped MatrixOrder in
theorem trace_product_nonneg {a : Space} {E ρ : Operator a}
    (hE : E.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (E * ρ).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (hρ.mul_mul_conjTranspose_same B).trace_nonneg

namespace Effect
variable {a : Space}

def probability (E : Effect a) (ρ : Density a) : ℝ := (E.matrix * ρ.matrix).trace.re

theorem probability_nonneg (E : Effect a) (ρ : Density a) : 0 ≤ E.probability ρ :=
  (Complex.nonneg_iff.mp (trace_product_nonneg E.positive ρ.positive)).1

theorem probability_le_one (E : Effect a) (ρ : Density a) : E.probability ρ ≤ 1 := by
  have h := (Complex.nonneg_iff.mp
    (trace_product_nonneg E.complement_positive ρ.positive)).1
  have he : ((1 - E.matrix) * ρ.matrix).trace.re = 1 - E.probability ρ := by
    simp [probability, Matrix.sub_mul, Matrix.trace_sub, ρ.normalized]
  rw [he] at h
  exact sub_nonneg.mp h

/-- Probabilities commute with channel execution and pulling the measurement back. -/
theorem probability_run {b : Space} (C : Channel a b) (E : Effect b) (ρ : Density a) :
    E.probability (C.run ρ) = (C.pullEffect E).probability ρ :=
  congrArg Complex.re (C.toKraus.trace_dual ρ.matrix E.matrix)

end Effect
end
end Foundation.Quantum
