import Foundation.Quantum.PartitionMeasurement
import Foundation.Quantum.BasisChannel

/-! Two diagonal measurements may be performed successively without measuring
any other basis coordinate. Equality retains both actual classical records
and the remaining quantum system, including arbitrary entangled auxiliaries. -/
namespace Foundation.Quantum.PartitionMeasurement
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a : Space} {m k : Nat}

theorem record_entry (f : a.Basis → Fin m) (ρ : Operator a)
    (r s : Fin m) (i j : a.Basis) :
    (instrument f).record.toKraus.apply ρ (r,i) (s,j) =
      if r = s ∧ f i = r ∧ f j = r then ρ i j else 0 := by
  by_cases h : r = s
  · subst s
    rw [Instrument.record_diagonal, branch_entry]
    simp
  · simp [Instrument.record, Kraus.apply, Instrument.recordOperator, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sigma,
      apply_ite, ite_mul, h, eq_comm]

theorem branches_commute (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (ρ : Operator a) (r : Fin m) (s : Fin k) :
    ((instrument g).branch s).apply (((instrument f).branch r).apply ρ) =
      ((instrument f).branch r).apply (((instrument g).branch s).apply ρ) := by
  ext i j
  simp only [branch_entry]
  by_cases hf : f i = r ∧ f j = r <;> by_cases hg : g i = s ∧ g j = s <;> simp [hf,hg]

abbrev pairCount (m k : Nat) := Fintype.card (Fin m × Fin k)

def together (f : a.Basis → Fin m) (g : a.Basis → Fin k) :
    a.Basis → Fin (pairCount m k) := fun i => Fintype.equivFin (Fin m × Fin k) (f i,g i)

def reorder (a : Space) (m k : Nat) :
    (Space.tensor (.register (pairCount m k)) a).Basis ≃
      (Space.tensor (.register k) (.tensor (.register m) a)).Basis where
  toFun p := let q := (Fintype.equivFin (Fin m × Fin k)).symm p.1; (q.2,(q.1,p.2))
  invFun p := (Fintype.equivFin (Fin m × Fin k) (p.2.1,p.1),p.2.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Record f first, keep the entire quantum output, and only then record g. -/
def sequential (f : a.Basis → Fin m) (g : a.Basis → Fin k) :
    Channel a (.tensor (.register k) (.tensor (.register m) a)) :=
  (instrument f).record.seq (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record

/-- One joint measurement, with its pair of labels stored in the same order. -/
def simultaneous (f : a.Basis → Fin m) (g : a.Basis → Fin k) :
    Channel a (.tensor (.register k) (.tensor (.register m) a)) :=
  (instrument (together f g)).record.seq (BasisChannel.channel (reorder a m k))

theorem sequential_eq (f : a.Basis → Fin m) (g : a.Basis → Fin k) (ρ : Operator a) :
    (sequential f g).toKraus.apply ρ = (simultaneous f g).toKraus.apply ρ := by
  change ((instrument f).record.toKraus.seq
    (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record.toKraus).apply ρ =
      ((instrument (together f g)).record.toKraus.seq
        (BasisChannel.channel (reorder a m k)).toKraus).apply ρ
  rw [Kraus.seq_apply, Kraus.seq_apply]
  rw [BasisChannel.apply]
  ext ⟨s,r,i⟩ ⟨t,q,j⟩
  change (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record.toKraus.apply
    ((instrument f).record.toKraus.apply ρ) (s,(r,i)) (t,(q,j)) =
      (instrument (together f g)).record.toKraus.apply ρ
        (Fintype.equivFin (Fin m × Fin k) (r,s),i)
        (Fintype.equivFin (Fin m × Fin k) (q,t),j)
  rw [record_entry (a := .tensor (.register m) a), record_entry (a := a), record_entry (a := a)]
  simp only [together, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hs : s = t <;> by_cases hr : r = q <;>
    by_cases hi : f i = r <;> by_cases hj : f j = r <;>
    by_cases hu : g i = s <;> by_cases hv : g j = s <;>
      simp_all

end
end Foundation.Quantum.PartitionMeasurement
