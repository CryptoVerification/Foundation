import Foundation.Quantum.Effects
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Hilbert--Schmidt Cauchy--Schwarz for actual finite Hermitian operators.
The proof uses the trace inner product, with local norm instances only; it does
not identify the operator norm with the Hilbert--Schmidt norm. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder InnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem trace_cauchy {e : Space} (A B : Operator e) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace.re)^2 ≤ (A*A).trace.re * (B*B).trace.re := by
  let : SeminormedAddCommGroup (Operator e) :=
    Matrix.toMatrixSeminormedAddCommGroup 1 Matrix.PosSemidef.one
  let : InnerProductSpace ℂ (Operator e) :=
    Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
  have hab := (Complex.abs_re_le_norm (inner ℂ A B)).trans (norm_inner_le_norm A B)
  have hnA := norm_sq_eq_re_inner (𝕜 := ℂ) A
  have hnB := norm_sq_eq_re_inner (𝕜 := ℂ) B
  change ‖A‖^2 = (A * 1 * A.conjTranspose).trace.re at hnA
  change ‖B‖^2 = (B * 1 * B.conjTranspose).trace.re at hnB
  change |(B * 1 * A.conjTranspose).trace.re| ≤ ‖A‖ * ‖B‖ at hab
  rw [hA.eq, Matrix.mul_one] at hnA hab
  rw [hB.eq, Matrix.mul_one] at hnB
  rw [Matrix.trace_mul_comm B A] at hab
  have hs := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg B)) |>.mpr hab
  simpa only [sq_abs, mul_pow, hnA, hnB] using hs

theorem trace_square_nonneg {e : Space} (A : Operator e) (hA : A.IsHermitian) :
    0 ≤ (A*A).trace.re := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hA.eq] at h
  exact (Complex.nonneg_iff.mp h.trace_nonneg).1

/-- The square-root form used to turn collision quantities into observation bounds. -/
theorem trace_cauchy_sqrt {e : Space} (A B : Operator e) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |(A*B).trace.re| ≤ Real.sqrt ((A*A).trace.re * (B*B).trace.re) := by
  have h := trace_cauchy A B hA hB
  have hpos := mul_nonneg (trace_square_nonneg A hA) (trace_square_nonneg B hB)
  have hs := Real.sq_sqrt hpos
  have hn := Real.sqrt_nonneg ((A*A).trace.re * (B*B).trace.re)
  nlinarith [sq_abs ((A*B).trace.re), abs_nonneg ((A*B).trace.re)]

end
end Foundation.Quantum
