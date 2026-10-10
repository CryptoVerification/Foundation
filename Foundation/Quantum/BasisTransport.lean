import Foundation.Quantum.OperatorDistance

/-! Reordering finite basis labels preserves every joint binary observation.
No subsystem is discarded and no quantum state is copied. -/
namespace Foundation.Quantum.BasisTransport
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

def operator (q : b.Basis ≃ a.Basis) (A : Operator a) : Operator b := A.submatrix q q

def pull (q : b.Basis ≃ a.Basis) (E : Effect b) : Effect a where
  matrix := E.matrix.submatrix q.symm q.symm
  positive := E.positive.submatrix q.symm
  complement_positive := by
    have h := E.complement_positive.submatrix q.symm
    have he : (1-E.matrix).submatrix q.symm q.symm = 1-E.matrix.submatrix q.symm q.symm := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    rw [he] at h
    exact h

theorem trace (q : b.Basis ≃ a.Basis) (A : Operator a) : (operator q A).trace = A.trace :=
  q.sum_comp (fun i => A i i)

theorem observation (q : b.Basis ≃ a.Basis) (E : Effect b) (A : Operator a) :
    (E.matrix * operator q A).trace = ((pull q E).matrix * A).trace := by
  have hE : (pull q E).matrix.submatrix q q = E.matrix := by
    ext i j
    simp [pull, Matrix.submatrix_apply]
  calc
    (E.matrix * operator q A).trace = (operator q ((pull q E).matrix * A)).trace := by
      unfold operator
      rw [← Matrix.submatrix_mul_equiv ((pull q E).matrix) A q q q, hE]
    _ = _ := trace q _

theorem approx (q : b.Basis ≃ a.Basis) (A B : Operator a) (ε : ℝ) (h : OperatorApprox A B ε) :
    OperatorApprox (operator q A) (operator q B) ε := by
  intro E
  rw [observation, observation]
  exact h (pull q E)

end
end Foundation.Quantum.BasisTransport
