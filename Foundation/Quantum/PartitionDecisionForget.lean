import Foundation.Quantum.PartitionDecision
import Foundation.Quantum.InstrumentForgetRecord

/-! Dropping the explicit accept/abort register after an error-first decision
recovers the actual sequential measurement. The decision only reads an
already classical label, so its nonselective action loses no further data. -/
namespace Foundation.Quantum.PartitionMeasurement
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a : Space} {m k : Nat}

theorem decision_forget (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] (ρ : Operator a) :
    (decideBefore f g P).forget.toKraus.apply ρ = (sequential f g).toKraus.apply ρ := by
  rw [Instrument.forget_apply]
  change _ = ((instrument f).record.toKraus.seq
    (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record.toKraus).apply ρ
  rw [Kraus.seq_apply]
  ext ⟨s,r,i⟩ ⟨t,q,j⟩
  simp only [Fin.sum_univ_two, Matrix.add_apply]
  rw [decision_entry, decision_entry, record_entry (a := .tensor (.register m) a), record_entry (a := a)]
  by_cases hst : s = t <;> by_cases hrq : r = q <;>
    by_cases hi : g i = s <;> by_cases hj : g j = s <;>
    by_cases hu : f i = r <;> by_cases hv : f j = r <;>
    by_cases hp : P r <;> simp_all

/-- Remove the actual decision register by a trace-preserving channel. -/
theorem decision_record_forget (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] (ρ : Operator a) :
    (Instrument.forgetRecord (.tensor (.register k) (.tensor (.register m) a)) 2).toKraus.apply
      ((decideBefore f g P).record.toKraus.apply ρ) = (sequential f g).toKraus.apply ρ := by
  rw [Instrument.forget_record, decision_forget]

end
end Foundation.Quantum.PartitionMeasurement
