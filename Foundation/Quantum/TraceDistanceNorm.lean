import Foundation.Quantum.TraceDistance
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Identify the Hermitian spectral formula with Tr sqrt(Aᴴ A). Matrix norm
instances are scoped locally; no global choice of matrix norm is changed. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace HermitianTrace
variable {a : Space} {A : Operator a}

theorem spectral_mul (h : A.IsHermitian) (f g : a.Basis → ℝ) :
    spectralMatrix h f * spectralMatrix h g = spectralMatrix h (fun i => f i * g i) := by
  unfold spectralMatrix
  simp only [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (h.eigenvectorUnitary : Operator a))]
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 2
  ext i j
  simp [Complex.ofReal_mul]

def absolute (h : A.IsHermitian) := spectralMatrix h (fun i => |h.eigenvalues i|)

theorem absolute_positive (h : A.IsHermitian) : (absolute h).PosSemidef :=
  spectral_positive h _ (fun _ => abs_nonneg _)

theorem absolute_square (h : A.IsHermitian) : absolute h * absolute h = A.conjTranspose * A := by
  have he : (fun i => |h.eigenvalues i| * |h.eigenvalues i|) =
      (fun i => h.eigenvalues i * h.eigenvalues i) := by
    funext i
    nlinarith [sq_abs (h.eigenvalues i)]
  calc
    _ = spectralMatrix h (fun i => |h.eigenvalues i| * |h.eigenvalues i|) := spectral_mul h _ _
    _ = spectralMatrix h (fun i => h.eigenvalues i * h.eigenvalues i) := congrArg _ he
    _ = spectralMatrix h h.eigenvalues * spectralMatrix h h.eigenvalues := (spectral_mul h _ _).symm
    _ = A * A := congrArg₂ (· * ·) (spectral_self h) (spectral_self h)
    _ = A.conjTranspose * A := by rw [h.eq]

theorem sqrt_gram_eq_absolute (h : A.IsHermitian) :
    CFC.sqrt (A.conjTranspose * A) = absolute h :=
  CFC.sqrt_unique (absolute_square h) (absolute_positive h).nonneg

theorem traceNorm_eq_sqrt_gram (h : A.IsHermitian) :
    traceNorm h = (CFC.sqrt (A.conjTranspose * A)).trace.re := by
  rw [sqrt_gram_eq_absolute, absolute, spectral_trace]
  rfl

end HermitianTrace

/-- Standard finite-matrix trace norm, independently of operational tests. -/
def matrixTraceNorm {a : Space} (A : Operator a) : ℝ := (CFC.sqrt (A.conjTranspose * A)).trace.re

theorem Density.traceDistance_eq_half_traceNorm {a : Space} (ρ σ : Density a) :
    Density.traceDistance ρ σ = (1 / 2 : ℝ) * matrixTraceNorm (ρ.matrix - σ.matrix) := by
  unfold Density.traceDistance matrixTraceNorm
  rw [HermitianTrace.traceNorm_eq_sqrt_gram]
  ring

end
end Foundation.Quantum
