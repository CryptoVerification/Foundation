import Foundation.Quantum.PartitionDiscard
import Foundation.Quantum.DiscardMiddleLocal

/-! Measuring a selected subsystem and discarding the unselected signal
equals measuring both signals and forgetting the unselected classical label.
The retained auxiliary system may be arbitrarily entangled with either. -/
namespace Foundation.Quantum.FirstRegister
noncomputable section
set_option backward.isDefEq.respectTransparency false

def associate (a b e : Space) :
    (Space.tensor (.tensor a b) e).Basis ≃ (Space.tensor a (.tensor b e)).Basis where
  toFun p := (p.1.1,(p.1.2,p.2))
  invFun p := ((p.1,p.2.1),p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def selectedDiscard (a b e : Space) :=
  ((BasisChannel.channel (associate a b e)).seq (channel a (.tensor b e))).seq
    (discardMiddle (.register (Fintype.card a.Basis)) b e)

theorem selectedDiscard_entry (a b e : Space) (ρ : Operator (.tensor (.tensor a b) e))
    (r s : Fin (Fintype.card a.Basis)) (u v : e.Basis) :
    (selectedDiscard a b e).toKraus.apply ρ (r,u) (s,v) =
      if r = s then ∑ x : b.Basis,
        ρ (((Fintype.equivFin a.Basis).symm r,x),u)
          (((Fintype.equivFin a.Basis).symm r,x),v) else 0 := by
  change (((BasisChannel.channel (associate a b e)).toKraus.seq (channel a (.tensor b e)).toKraus).seq
    (discardMiddle (.register (Fintype.card a.Basis)) b e).toKraus).apply ρ _ _ = _
  rw [Kraus.seq_apply, Kraus.seq_apply, discardMiddle_apply]
  have h (x : b.Basis) := apply_entry a (.tensor b e)
    ((BasisChannel.channel (associate a b e)).toKraus.apply ρ)
    ((Fintype.equivFin a.Basis).symm r) ((Fintype.equivFin a.Basis).symm s) (x,u) (x,v)
  simp only [Equiv.apply_symm_apply, (Fintype.equivFin a.Basis).symm.injective.eq_iff] at h
  simp_rw [h]
  rw [BasisChannel.apply]
  by_cases hrs : r = s
  · subst s
    simp only [ite_true]
    rfl
  · simp [hrs]

theorem selectedDiscard_eq (a b e : Space) (ρ : Operator (.tensor (.tensor a b) e)) :
    (selectedDiscard a b e).toKraus.apply ρ =
      (PartitionMeasurement.discardSignal (fun p : (Space.tensor a b).Basis =>
        Fintype.equivFin a.Basis p.1) e).toKraus.apply ρ := by
  ext ⟨r,u⟩ ⟨s,v⟩
  rw [selectedDiscard_entry, PartitionMeasurement.discard_entry]
  by_cases hrs : r = s
  · subst s
    simp only [ite_true, Fintype.sum_prod_type]
    simp only [← Equiv.eq_symm_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp [hrs]

theorem selectedDiscard_full (a b e : Space) (ρ : Operator (.tensor (.tensor a b) e)) :
    (selectedDiscard a b e).toKraus.apply ρ =
      (classicalMap e (fun r => Fintype.equivFin a.Basis
        (((Fintype.equivFin (Space.tensor a b).Basis).symm r).1))).toKraus.apply
          ((channel (.tensor a b) e).toKraus.apply ρ) :=
  (selectedDiscard_eq a b e ρ).trans (PartitionMeasurement.discard_eq _ ρ)

/-- A local basis operation on the unrecorded subsystem commutes with
recording the selected label, retaining every unmatched quantum coordinate. -/
theorem local_record (a b e : Space) (U : Operator b)
    (ρ : Operator (.tensor a (.tensor b e))) :
    (channel a (.tensor b e)).toKraus.apply
      ((Kraus.single (Op.tensor (Op.ident a) (Op.tensor U (Op.ident e)))).apply ρ) =
    (Kraus.single (Op.tensor (Op.ident (.register (Fintype.card a.Basis)))
      (Op.tensor U (Op.ident e)))).apply ((channel a (.tensor b e)).toKraus.apply ρ) := by
  ext ⟨r,x,u⟩ ⟨s,y,v⟩
  obtain ⟨i,rfl⟩ := (Fintype.equivFin a.Basis).surjective r
  obtain ⟨j,rfl⟩ := (Fintype.equivFin a.Basis).surjective s
  rw [apply_entry, middle_local_entry (.register (Fintype.card a.Basis)) b e U]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, middle_local_entry a b e U]
    have hb : Matrix.of (fun r s =>
        (channel a (.tensor b e)).toKraus.apply ρ
          (Fintype.equivFin a.Basis i,r,u) (Fintype.equivFin a.Basis i,s,v)) =
        Matrix.of (fun r s => ρ (i,r,u) (i,s,v)) := by
      ext r s
      simp only [Matrix.of_apply]
      rw [apply_entry a (.tensor b e)]
      simp only [ite_true]
    rw [hb]
  · rw [if_neg h]
    have hb : Matrix.of (fun r s =>
        (channel a (.tensor b e)).toKraus.apply ρ
          (Fintype.equivFin a.Basis i,r,u) (Fintype.equivFin a.Basis j,s,v)) =
        (0 : Operator b) := by
      ext r s
      simp only [Matrix.of_apply, Matrix.zero_apply]
      rw [apply_entry a (.tensor b e)]
      simp only [h, ite_false]
    rw [hb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]

theorem discard_local_record (a b e : Space) (U : Operator b) (hU : U.conjTranspose * U = 1)
    (ρ : Operator (.tensor a (.tensor b e))) :
    (discardMiddle (.register (Fintype.card a.Basis)) b e).toKraus.apply
      ((channel a (.tensor b e)).toKraus.apply
        ((Kraus.single (Op.tensor (Op.ident a) (Op.tensor U (Op.ident e)))).apply ρ)) =
    (discardMiddle (.register (Fintype.card a.Basis)) b e).toKraus.apply
      ((channel a (.tensor b e)).toKraus.apply ρ) := by
  rw [local_record, discardMiddle_local _ _ _ U hU]

end
end Foundation.Quantum.FirstRegister
