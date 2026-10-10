import Foundation.Quantum.ClassicalMap
import Foundation.Quantum.BasisChannel

/-! Measuring the first subsystem and recording its finite basis label,
while retaining every matrix coordinate of the second subsystem. -/
namespace Foundation.Quantum.FirstRegister
noncomputable section
set_option backward.isDefEq.respectTransparency false

def operator (a e : Space) (x : a.Basis) :
    Op (.tensor a e) (.tensor (.register (Fintype.card a.Basis)) e) :=
  fun i j => if i.1 = Fintype.equivFin a.Basis x ∧ j.1 = x ∧ i.2 = j.2 then 1 else 0

theorem complete (a e : Space) :
    (∑ x, (operator a e x).conjTranspose * operator a e x) = 1 := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [operator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, apply_ite, eq_comm,
    -Finset.sum_boole]
  by_cases hi : i = j <;> by_cases hu : u = v <;> simp_all

def channel (a e : Space) :
    Channel (.tensor a e) (.tensor (.register (Fintype.card a.Basis)) e) where
  index := a.Basis
  finite := inferInstance
  operator := operator a e
  complete := complete a e

theorem apply_entry (a e : Space) (ρ : Operator (.tensor a e))
    (x y : a.Basis) (u v : e.Basis) :
    (channel a e).toKraus.apply ρ (Fintype.equivFin a.Basis x,u) (Fintype.equivFin a.Basis y,v) =
      if x = y then ρ (x,u) (x,v) else 0 := by
  simp [channel, Kraus.apply, operator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, ite_mul,
    apply_ite, -Finset.sum_boole]
  by_cases h : x = y <;> simp_all

/-- Permuting quantum basis directions before measuring equals permuting
the actual classical record afterwards, with the whole auxiliary retained. -/
theorem relabel (a e : Space) (q : a.Basis ≃ a.Basis)
    (ρ : Operator (.tensor a e)) :
    (channel a e).toKraus.apply (((BasisChannel.channel q).amplify e).toKraus.apply ρ) =
      (classicalMap e (fun r => Fintype.equivFin a.Basis
        (q ((Fintype.equivFin a.Basis).symm r)))).toKraus.apply ((channel a e).toKraus.apply ρ) := by
  have lift : ((BasisChannel.channel q).amplify e).toKraus.apply ρ =
      fun i j => ρ (q.symm i.1,i.2) (q.symm j.1,j.2) := by
    change (Kraus.single (Op.tensor (Op.basisMap q) (Op.ident e))).apply ρ = _
    rw [Kraus.single_apply]
    ext ⟨i,u⟩ ⟨j,v⟩
    simp [Op.tensor, Op.ident, Op.basisMap, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ← q.symm_apply_eq, ite_mul, apply_ite]
  ext ⟨r,u⟩ ⟨s,v⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin a.Basis).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin a.Basis).surjective s
  rw [apply_entry, lift, classicalMap_apply]
  simp only [Equiv.apply_eq_iff_eq]
  have record (t : Fin (Fintype.card a.Basis)) :=
    apply_entry a e ρ ((Fintype.equivFin a.Basis).symm t) ((Fintype.equivFin a.Basis).symm t) u v
  simp only [Equiv.apply_symm_apply, ite_true] at record
  simp_rw [record]
  by_cases h : x = y
  · subst y
    simp only [ite_true]
    change ρ (q.symm x,u) (q.symm x,v) =
      ∑ t, if q ((Fintype.equivFin a.Basis).symm t) = x then
        ρ ((Fintype.equivFin a.Basis).symm t,u) ((Fintype.equivFin a.Basis).symm t,v) else 0
    symm
    exact (Equiv.sum_comp (Fintype.equivFin a.Basis).symm
      (fun z => if q z = x then ρ (z,u) (z,v) else 0)).trans (by simp [← q.eq_symm_apply])
  · simp only [h, ite_false]

end
end Foundation.Quantum.FirstRegister
