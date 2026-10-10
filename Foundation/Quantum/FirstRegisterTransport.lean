import Foundation.Quantum.FirstRegister

/-! Measurement records are transported across distinct finite quantum spaces,
not just permutations of one fixed space. The auxiliary remains quantum. -/
namespace Foundation.Quantum.FirstRegister
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Transporting between quantum spaces before measuring equals transporting
the actual classical record afterwards, with the whole auxiliary retained. -/
theorem transport (a b e : Space) (q : a.Basis ≃ b.Basis)
    (ρ : Operator (.tensor a e)) :
    (channel b e).toKraus.apply (((BasisChannel.channel q).amplify e).toKraus.apply ρ) =
      (classicalMap e (fun r => Fintype.equivFin b.Basis
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
  obtain ⟨x,rfl⟩ := (Fintype.equivFin b.Basis).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin b.Basis).surjective s
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
