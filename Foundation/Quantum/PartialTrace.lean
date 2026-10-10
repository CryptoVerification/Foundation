import Foundation.Quantum.Channels

/-! Physical discard of a subsystem, distinct from the amplitude-level erase
in a classical Frobenius structure. It accepts arbitrary entangled states. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

def traceOperator (a e : Space) (r : e.Basis) : Op (.tensor a e) a :=
  fun i j => if i = j.1 ∧ r = j.2 then 1 else 0

theorem traceOperator_complete (a e : Space) :
    (∑ r, (traceOperator a e r).conjTranspose * traceOperator a e r) =
      (1 : Operator (.tensor a e)) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp [traceOperator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, ite_and, Prod.mk.injEq, eq_comm, apply_ite]
  split_ifs <;> simp_all

def discardRight (a e : Space) : Channel (.tensor a e) a where
  index := e.Basis
  finite := inferInstance
  operator := traceOperator a e
  complete := traceOperator_complete a e

theorem discardRight_apply (a e : Space) (ρ : Operator (.tensor a e)) (i j : a.Basis) :
    (discardRight a e).toKraus.apply ρ i j = ∑ r : e.Basis, ρ (i, r) (j, r) := by
  simp [discardRight, Kraus.apply, traceOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Space.Basis,
    ite_and, apply_ite, ite_mul, -Finset.sum_boole]

end
end Foundation.Quantum
