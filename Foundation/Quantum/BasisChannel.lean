import Foundation.Quantum.Channels
import Foundation.Quantum.Category
import Foundation.Quantum.BasisTransport

/-! A finite basis equivalence gives a physical reversible channel. This
implements basis transport without discarding any quantum subsystem. -/
namespace Foundation.Quantum.BasisChannel
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

theorem isometry (q : a.Basis ≃ b.Basis) :
    (Op.basisMap q).conjTranspose * Op.basisMap q = 1 := by
  ext i j
  simp [Op.basisMap, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, q.injective.eq_iff, eq_comm]

def channel (q : a.Basis ≃ b.Basis) : Channel a b :=
  Channel.ofIsometry (Op.basisMap q) (isometry q)

theorem apply (q : a.Basis ≃ b.Basis) (ρ : Operator a) :
    (channel q).toKraus.apply ρ = BasisTransport.operator q.symm ρ := by
  change (Kraus.single (Op.basisMap q)).apply ρ = _
  rw [Kraus.single_apply]
  ext i j
  simp [Op.basisMap, Matrix.mul_apply, Matrix.conjTranspose_apply, BasisTransport.operator,
    Matrix.submatrix_apply, ← q.symm_apply_eq, ite_mul, mul_ite]

/-- Reversible basis transport retains every coordinate of a quantum auxiliary. -/
theorem amplify_apply (e : Space) (q : a.Basis ≃ b.Basis)
    (ρ : Operator (.tensor a e)) :
    ((channel q).amplify e).toKraus.apply ρ =
      Matrix.of (fun i j => ρ (q.symm i.1,i.2) (q.symm j.1,j.2)) := by
  change (Kraus.single (Op.tensor (Op.basisMap q) (Op.ident e))).apply ρ = _
  rw [Kraus.single_apply]
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [Op.tensor, Op.ident, Op.basisMap, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Matrix.of_apply, ← q.symm_apply_eq, ite_mul, apply_ite]

end
end Foundation.Quantum.BasisChannel
