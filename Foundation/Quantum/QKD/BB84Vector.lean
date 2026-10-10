import Foundation.Quantum.QKD.BB84Complementary
import Foundation.Quantum.VectorEffect

/-! Hilbert-space estimates for a BB84 dilation. The bounds use Euclidean
norms and are independent of the size of the retained finite environment. -/
namespace Foundation.Quantum.QKD.BB84Attack
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
variable {e : Space}

def component (V : BB84Attack e) (i b : Fin 2) : HilbertSpace e :=
  WithLp.toLp 2 (fun u => V.dilation (i,u) b)

@[simp] theorem component_apply (V : BB84Attack e) (i b : Fin 2) (u : e.Basis) :
    V.component i b u = V.dilation (i,u) b := rfl

theorem component_norm_sq (V : BB84Attack e) (i b : Fin 2) :
    ‖V.component i b‖ ^ 2 = ∑ u : e.Basis, Complex.normSq (V.dilation (i,u) b) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [component_apply, Complex.normSq_eq_norm_sq]

theorem column_normalized (V : BB84Attack e) (b : Fin 2) :
    ‖V.component 0 b‖ ^ 2 + ‖V.component 1 b‖ ^ 2 = 1 := by
  have h := congrFun (congrFun V.isometry b) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ite_true] at h
  have hr := congrArg Complex.re h
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.add_re, Complex.re_sum,
    Complex.star_def, Complex.one_re] at hr
  have hz (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    rw [mul_comm, Complex.mul_conj]
    rfl
  simp_rw [hz] at hr
  simpa only [component_norm_sq] using hr

theorem component_norm_le_one (V : BB84Attack e) (i b : Fin 2) :
    ‖V.component i b‖ ≤ 1 := by
  have h := V.column_normalized b
  fin_cases i
  · change ‖V.component 0 b‖ ≤ 1
    nlinarith [sq_nonneg ‖V.component 1 b‖, norm_nonneg (V.component 0 b)]
  · change ‖V.component 1 b‖ ≤ 1
    nlinarith [sq_nonneg ‖V.component 0 b‖, norm_nonneg (V.component 1 b)]

theorem zError_norm (V : BB84Attack e) (b : Fin 2) :
    V.zError b = ‖V.component (1-b) b‖ ^ 2 := (V.component_norm_sq (1-b) b).symm

def residual (V : BB84Attack e) : HilbertSpace e :=
  V.component 0 0 + V.component 0 1 - V.component 1 0 - V.component 1 1

theorem xPlusError_norm (V : BB84Attack e) : V.xPlusError = ‖V.residual‖ ^ 2 / 4 := by
  simp [xPlusError, EuclideanSpace.norm_sq_eq, residual, Complex.normSq_eq_norm_sq]

theorem residual_norm (V : BB84Attack e) : ‖V.residual‖ = 2 * Real.sqrt V.xPlusError := by
  rw [xPlusError_norm, Real.sqrt_div (sq_nonneg _)]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1; norm_num
  rw [h4, Real.sqrt_sq (norm_nonneg _)]
  ring

theorem wrong_norm (V : BB84Attack e) (b : Fin 2) :
    ‖V.component (1-b) b‖ = Real.sqrt (V.zError b) := by
  rw [zError_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Disturbance in both bases bounds the distance between the correct environment vectors. -/
theorem correct_vector_distance (V : BB84Attack e) :
    ‖V.component 0 0 - V.component 1 1‖ ≤
      2 * Real.sqrt V.xPlusError + Real.sqrt (V.zError 0) + Real.sqrt (V.zError 1) := by
  have he : V.component 0 0 - V.component 1 1 =
      V.residual + (V.component 1 0 - V.component 0 1) := by
    unfold residual
    abel
  calc
    _ = ‖V.residual + (V.component 1 0 - V.component 0 1)‖ := congrArg norm he
    _ ≤ ‖V.residual‖ + ‖V.component 1 0 - V.component 0 1‖ := norm_add_le _ _
    _ ≤ ‖V.residual‖ + (‖V.component 1 0‖ + ‖V.component 0 1‖) :=
      add_le_add le_rfl (norm_sub_le _ _)
    _ = _ := by
      have h0 : ‖V.component 1 0‖ = Real.sqrt (V.zError 0) := by simpa using V.wrong_norm 0
      have h1 : ‖V.component 0 1‖ = Real.sqrt (V.zError 1) := by simpa using V.wrong_norm 1
      rw [residual_norm, h0, h1]
      ring

end
end Foundation.Quantum.QKD.BB84Attack
