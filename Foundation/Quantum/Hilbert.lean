import Foundation.Quantum.Semantics
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The matrix model is a model on actual finite-dimensional complex Hilbert
spaces, rather than just a formal matrix algebra. Completeness and the inner
product are supplied by mathlib's EuclideanSpace. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev HilbertSpace (a : Space) := EuclideanSpace ℂ a.Basis

namespace Op

def linear {a b} (M : Op a b) : HilbertSpace a →ₗ[ℂ] HilbertSpace b :=
  Matrix.toEuclideanLin M

theorem linear_injective (a b : Space) : Function.Injective (linear (a := a) (b := b)) :=
  Matrix.toEuclideanLin.injective

theorem linear_dagger {a b} (M : Op a b) : linear (dagger M) = (linear M).adjoint :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint M

theorem linear_seq {a b c} (M : Op a b) (N : Op b c) :
    linear (seq M N) = (linear N).comp (linear M) := by
  ext x i
  simp [linear, seq, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
end Op

/-- The same interpreted proof gives equality of genuine Hilbert-space maps. -/
theorem qkd_hilbert (σ : Assignment) {a b} (m : Term a b)
    (measurement : Op.seq (Op.dagger (m.eval σ)) (m.eval σ) = Op.ident b) :
    Op.linear ((Term.alice m).eval σ) = Op.linear ((Term.bob m).eval σ) :=
  congrArg Op.linear (qkd_correct σ m measurement)

end
end Foundation.Quantum
