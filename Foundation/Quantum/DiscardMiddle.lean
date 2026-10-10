import Foundation.Quantum.PartialTrace

/-! Physical partial trace of a middle subsystem. The first and last systems
can remain correlated; no separability assumption is used. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

def traceMiddleOperator (a b c : Space) (r : b.Basis) :
    Op (.tensor a (.tensor b c)) (.tensor a c) := fun i j =>
  if i.1 = j.1 ∧ r = j.2.1 ∧ i.2 = j.2.2 then 1 else 0

theorem traceMiddle_complete (a b c : Space) :
    (∑ r, (traceMiddleOperator a b c r).conjTranspose * traceMiddleOperator a b c r) = 1 := by
  ext ⟨i,r,u⟩ ⟨j,s,v⟩
  simp [traceMiddleOperator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_and, mul_ite,
    Prod.mk.injEq, eq_comm, -Finset.sum_boole]
  split_ifs <;> simp_all

def discardMiddle (a b c : Space) : Channel (.tensor a (.tensor b c)) (.tensor a c) where
  index := b.Basis
  finite := inferInstance
  operator := traceMiddleOperator a b c
  complete := traceMiddle_complete a b c

theorem discardMiddle_apply (a b c : Space) (ρ : Operator (.tensor a (.tensor b c)))
    (i j : a.Basis) (u v : c.Basis) :
    (discardMiddle a b c).toKraus.apply ρ (i,u) (j,v) =
      ∑ r : b.Basis, ρ (i,r,u) (j,r,v) := by
  simp [discardMiddle, Kraus.apply, traceMiddleOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, ite_mul,
    apply_ite, -Finset.sum_boole]

end
end Foundation.Quantum
