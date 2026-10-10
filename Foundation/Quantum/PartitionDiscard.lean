import Foundation.Quantum.PartitionDelay
import Foundation.Quantum.FirstRegister
import Foundation.Quantum.DiscardMiddle

/-! Discarding the measured signal equates a coarse record with a complete
signal measurement followed by forgetting the extra classical information.
All auxiliary coherences are retained; intermediate quantum states need not
be equal before the signal is discarded. -/
namespace Foundation.Quantum.PartitionMeasurement
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {a e : Space} {m : Nat}

def discardSignal (f : a.Basis → Fin m) (e : Space) :
    Channel (.tensor a e) (.tensor (.register m) e) :=
  (instrument (fun p : (Space.tensor a e).Basis => f p.1)).record.seq
    (discardMiddle (.register m) a e)

theorem discard_entry (f : a.Basis → Fin m) (ρ : Operator (.tensor a e))
    (r s : Fin m) (u v : e.Basis) :
    (discardSignal f e).toKraus.apply ρ (r,u) (s,v) =
      if r = s then ∑ x : a.Basis, if f x = r then ρ (x,u) (x,v) else 0 else 0 := by
  change (((instrument (fun p : (Space.tensor a e).Basis => f p.1)).record).toKraus.seq
    (discardMiddle (.register m) a e).toKraus).apply ρ _ _ = _
  rw [Kraus.seq_apply, discardMiddle_apply]
  simp_rw [record_entry (a := .tensor a e)]
  by_cases h : r = s <;> simp [h]

theorem discard_eq (f : a.Basis → Fin m) (ρ : Operator (.tensor a e)) :
    (discardSignal f e).toKraus.apply ρ =
      (classicalMap e (fun t => f ((Fintype.equivFin a.Basis).symm t))).toKraus.apply
        ((FirstRegister.channel a e).toKraus.apply ρ) := by
  ext ⟨r,u⟩ ⟨s,v⟩
  rw [discard_entry, classicalMap_apply]
  have hr (t : Fin (Fintype.card a.Basis)) :=
    FirstRegister.apply_entry a e ρ ((Fintype.equivFin a.Basis).symm t)
      ((Fintype.equivFin a.Basis).symm t) u v
  simp only [Equiv.apply_symm_apply, ite_true] at hr
  simp_rw [hr]
  by_cases h : r = s
  · simp only [h, ite_true]
    exact (Equiv.sum_comp (Fintype.equivFin a.Basis).symm
      (fun x => if f x = s then ρ (x,u) (x,v) else 0)).symm
  · simp [h]

/-- Sequentially record f and g, flatten the two classical labels, then
trace out only the signal, leaving the auxiliary quantum system. -/
def sequentialDiscard (f : a.Basis → Fin m) {k : Nat} (g : a.Basis → Fin k) (e : Space) :
    Channel (.tensor a e) (.tensor (.register (pairCount m k)) e) :=
  ((sequential (fun p : (Space.tensor a e).Basis => f p.1) (fun p => g p.1)).seq
    (BasisChannel.channel (reorder (.tensor a e) m k).symm)).seq
      (discardMiddle (.register (pairCount m k)) a e)

theorem sequential_discard_eq (f : a.Basis → Fin m) {k : Nat} (g : a.Basis → Fin k)
    (ρ : Operator (.tensor a e)) :
    (sequentialDiscard f g e).toKraus.apply ρ = (discardSignal (together f g) e).toKraus.apply ρ := by
  change (((sequential (fun p : (Space.tensor a e).Basis => f p.1) (fun p => g p.1)).toKraus.seq
    (BasisChannel.channel (reorder (.tensor a e) m k).symm).toKraus).seq
      (discardMiddle (.register (pairCount m k)) a e).toKraus).apply ρ =
    (((instrument (fun p : (Space.tensor a e).Basis => together f g p.1)).record).toKraus.seq
      (discardMiddle (.register (pairCount m k)) a e).toKraus).apply ρ
  rw [Kraus.seq_apply, Kraus.seq_apply, Kraus.seq_apply, sequential_eq]
  congr 1
  change (BasisChannel.channel (reorder (.tensor a e) m k).symm).toKraus.apply
    ((((instrument (fun p : (Space.tensor a e).Basis => together f g p.1)).record).toKraus.seq
      (BasisChannel.channel (reorder (.tensor a e) m k)).toKraus).apply ρ) = _
  rw [Kraus.seq_apply, BasisChannel.apply, BasisChannel.apply]
  ext i j
  simp [BasisTransport.operator, Matrix.submatrix_apply]

end
end Foundation.Quantum.PartitionMeasurement
