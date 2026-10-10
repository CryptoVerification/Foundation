import Foundation.Quantum.Hilbert
import Foundation.Quantum.Effects

/-! Quantitative bounds for effects on subnormalized pure vectors. All effects
are derived from the existing positive/complement-positive matrix definition;
no operator-norm contraction is added as a premise. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder

namespace Op

theorem linear_mul {a b c : Space} (M : Op b c) (N : Op a b) :
    linear (M * N) = (linear M).comp (linear N) := linear_seq N M

@[simp] theorem linear_one (a : Space) : linear (1 : Operator a) = LinearMap.id := by
  ext x i
  simp [linear, Matrix.toEuclideanLin]

end Op

namespace Effect
variable {a : Space}

/-- Born weight for a vector that need not have norm one. -/
def weight (E : Effect a) (x : HilbertSpace a) : ℝ :=
  (E.matrix * Matrix.vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))).trace.re

theorem weight_eq_inner (E : Effect a) (x : HilbertSpace a) :
    E.weight x = (inner ℂ x (Op.linear E.matrix x)).re := by
  unfold weight
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rfl

theorem weight_nonneg (E : Effect a) (x : HilbertSpace a) : 0 ≤ E.weight x :=
  (Complex.nonneg_iff.mp (trace_product_nonneg E.positive
    (Matrix.posSemidef_vecMulVec_self_star _))).1

theorem weight_le_norm_sq (E : Effect a) (x : HilbertSpace a) : E.weight x ≤ ‖x‖ ^ 2 := by
  have h := (Complex.nonneg_iff.mp (trace_product_nonneg E.complement_positive
    (Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp x)))).1
  have ht : (Matrix.vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))).trace.re = ‖x‖ ^ 2 := by
    rw [Matrix.trace_vecMulVec]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    ht, weight, sub_nonneg] using h

theorem weight_factor (E : Effect a) (B : Operator a)
    (hB : E.matrix = B.conjTranspose * B) (x : HilbertSpace a) :
    E.weight x = ‖Op.linear B x‖ ^ 2 := by
  rw [weight_eq_inner, hB, Op.linear_mul]
  change (inner ℂ x (Op.linear B.conjTranspose (Op.linear B x))).re = _
  have hAdj : Op.linear B.conjTranspose = (Op.linear B).adjoint := Op.linear_dagger B
  rw [hAdj]
  rw [LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

/-- A square-root factor of an effect contracts every vector. -/
theorem factor_contract (E : Effect a) (B : Operator a)
    (hB : E.matrix = B.conjTranspose * B) (x : HilbertSpace a) :
    ‖Op.linear B x‖ ≤ ‖x‖ := by
  have h := E.weight_le_norm_sq x
  rw [E.weight_factor B hB x] at h
  nlinarith [norm_nonneg (Op.linear B x), norm_nonneg x]

open scoped MatrixOrder in
/-- A dimension-independent perturbation bound, including subnormalized vectors. -/
theorem weight_sub_bound (E : Effect a) (x y : HilbertSpace a) :
    |E.weight x - E.weight y| ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp E.positive.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  rw [E.weight_factor B hB x, E.weight_factor B hB y]
  have hd : |‖Op.linear B x‖ - ‖Op.linear B y‖| ≤ ‖x - y‖ := by
    calc
      _ ≤ ‖Op.linear B x - Op.linear B y‖ := abs_norm_sub_norm_le _ _
      _ = ‖Op.linear B (x - y)‖ := by rw [map_sub]
      _ ≤ ‖x - y‖ := E.factor_contract B hB _
  have hs := add_le_add (E.factor_contract B hB x) (E.factor_contract B hB y)
  calc
    _ = |‖Op.linear B x‖ - ‖Op.linear B y‖| * (‖Op.linear B x‖ + ‖Op.linear B y‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
      congr 1
      ring
    _ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := mul_le_mul hd hs
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := mul_comm _ _

end Effect
end
end Foundation.Quantum
