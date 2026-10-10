import Foundation.Quantum.PartitionDiscard
import Foundation.Quantum.InstrumentPost

/-! Measuring a basis and then discarding the measured signal gives the
same complete classical/auxiliary record as FirstRegister. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem basis_record_discard (a e : Space) (ρ : Operator (.tensor a e)) :
    (discardMiddle (.register (Fintype.card a.Basis)) a e).toKraus.apply
      (((basisInstrument a).amplify e).record.toKraus.apply ρ) =
      (FirstRegister.channel a e).toKraus.apply ρ := by
  have hop (r : Fin (Fintype.card a.Basis)) :
      Op.tensor (projector a ((Fintype.equivFin a.Basis).symm r)) (Op.ident e) =
        QKD.QuantumErrorTest.mask (fun p : (Space.tensor a e).Basis => Fintype.equivFin a.Basis p.1 = r) := by
    ext ⟨i,u⟩ ⟨j,v⟩
    simp [projector, Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap,
      QKD.QuantumErrorTest.mask, Matrix.diagonal_apply, Matrix.one_apply,
      ← Equiv.eq_symm_apply, Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases huv : u = v <;> simp_all
    all_goals aesop
  have hr : ((basisInstrument a).amplify e).record.toKraus.apply ρ =
      (PartitionMeasurement.instrument
        (fun p : (Space.tensor a e).Basis => Fintype.equivFin a.Basis p.1)).record.toKraus.apply ρ := by
    apply Instrument.record_congr
    intro r
    change (Kraus.single (Op.tensor (projector a ((Fintype.equivFin a.Basis).symm r)) (Op.ident e))).apply ρ = _
    rw [hop]
    rfl
  rw [hr, ← Kraus.seq_apply]
  change (PartitionMeasurement.discardSignal (fun x => Fintype.equivFin a.Basis x) e).toKraus.apply ρ = _
  rw [PartitionMeasurement.discard_eq]
  ext ⟨r,u⟩ ⟨s,v⟩
  rw [classicalMap_apply]
  simp only [Equiv.apply_symm_apply]
  by_cases h : r = s
  · subst s
    simp only [ite_true, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [h, ite_false]
    obtain ⟨x,rfl⟩ := (Fintype.equivFin a.Basis).surjective r
    obtain ⟨y,rfl⟩ := (Fintype.equivFin a.Basis).surjective s
    rw [FirstRegister.apply_entry]
    simp_all

end
end Foundation.Quantum
