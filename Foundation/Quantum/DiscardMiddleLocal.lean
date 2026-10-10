import Foundation.Quantum.DiscardMiddle
import Foundation.Quantum.QKD.Qubits

/-! A local isometric basis operation on a subsystem that is subsequently
discarded cannot alter any retained joint matrix block. No separability or
normalization assumption is imposed on the input operator. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem middle_local_entry (a b e : Space) (U : Operator b)
    (ρ : Operator (.tensor a (.tensor b e))) (i j : a.Basis) (x y : b.Basis) (u v : e.Basis) :
    (Kraus.single (Op.tensor (Op.ident a) (Op.tensor U (Op.ident e)))).apply ρ (i,x,u) (j,y,v) =
      (U * Matrix.of (fun r s => ρ (i,r,u) (j,s,v)) * U.conjTranspose) x y := by
  simp [Kraus.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, apply_ite, Finset.sum_mul, mul_assoc, Matrix.of_apply]

theorem discardMiddle_local (a b e : Space) (U : Operator b) (hU : U.conjTranspose * U = 1)
    (ρ : Operator (.tensor a (.tensor b e))) :
    (discardMiddle a b e).toKraus.apply
      ((Kraus.single (Op.tensor (Op.ident a) (Op.tensor U (Op.ident e)))).apply ρ) =
      (discardMiddle a b e).toKraus.apply ρ := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [discardMiddle_apply, discardMiddle_apply]
  simp_rw [middle_local_entry a b e U ρ i j]
  change (U * Matrix.of (fun r s => ρ (i,r,u) (j,s,v)) * U.conjTranspose).trace =
    (Matrix.of (fun r s => ρ (i,r,u) (j,s,v))).trace
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

end
end Foundation.Quantum
