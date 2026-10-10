import Foundation.Quantum.PartitionDelay
import Foundation.Quantum.InstrumentPost

/-! Moving a public binary decision based only on the first measurement
record across the second measurement. Both accepted and rejected branches
are retained, with the remaining quantum systems. -/
namespace Foundation.Quantum.PartitionMeasurement
noncomputable section
open QKD.QuantumErrorTest
set_option backward.isDefEq.respectTransparency false
variable {a : Space} {m k : Nat}

theorem test_entry (P : a.Basis → Prop) [DecidablePred P] (d : Fin 2)
    (ρ : Operator a) (i j : a.Basis) :
    ((test P).branch d).apply ρ i j =
      if (if d = 0 then P i else ¬P i) ∧ (if d = 0 then P j else ¬P j) then ρ i j else 0 := by
  change (Kraus.single (mask (fun i => if d = 0 then P i else ¬P i))).apply ρ i j = _
  rw [Kraus.single_apply, mask_adjoint]
  by_cases hi : (if d = 0 then P i else ¬P i) <;>
    by_cases hj : (if d = 0 then P j else ¬P j) <;>
      simp [mask, Matrix.diagonal_mul, Matrix.mul_diagonal, hi,hj]

/-- Record the first outcome, decide, then measure the second outcome. -/
def decideBefore (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] :
    Instrument a (.tensor (.register k) (.tensor (.register m) a)) 2 :=
  ((test (fun p : (Space.tensor (.register m) a).Basis => P p.1)).pre
    (instrument f).record).post
      (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record

/-- Measure both outcomes, then make the same public decision. -/
def decideAfter (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] :
    Instrument a (.tensor (.register k) (.tensor (.register m) a)) 2 :=
  (test (fun p : (Space.tensor (.register k) (.tensor (.register m) a)).Basis => P p.2.1)).pre
    (sequential f g)

theorem decision_branch (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] (d : Fin 2) (ρ : Operator a) :
    ((decideBefore f g P).branch d).apply ρ = ((decideAfter f g P).branch d).apply ρ := by
  dsimp only [decideBefore, decideAfter]
  rw [Instrument.post_apply, Instrument.pre_apply, Instrument.pre_apply]
  change _ = ((test (fun p : (Space.tensor (.register k) (.tensor (.register m) a)).Basis => P p.2.1)).branch d).apply
    (((instrument f).record.toKraus.seq
      (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record.toKraus).apply ρ)
  rw [Kraus.seq_apply]
  ext ⟨s,r,i⟩ ⟨t,q,j⟩
  rw [record_entry (a := .tensor (.register m) a), test_entry,
    test_entry, record_entry (a := .tensor (.register m) a)]
  by_cases hst : s = t <;> by_cases hd : d = 0 <;>
    by_cases hr : P r <;> by_cases hq : P q <;>
    simp_all

/-- Explicit accepted or rejected quantum block, with both labels retained. -/
theorem decision_entry (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] (d : Fin 2) (ρ : Operator a)
    (s t : Fin k) (r q : Fin m) (i j : a.Basis) :
    ((decideBefore f g P).branch d).apply ρ (s,(r,i)) (t,(q,j)) =
      if (if d = 0 then P r else ¬P r) ∧ (if d = 0 then P q else ¬P q) then
        if s = t ∧ g i = s ∧ g j = s then
          if r = q ∧ f i = r ∧ f j = r then ρ i j else 0
        else 0
      else 0 := by
  rw [decision_branch]
  dsimp only [decideAfter]
  rw [Instrument.pre_apply]
  change ((test (fun p : (Space.tensor (.register k) (.tensor (.register m) a)).Basis => P p.2.1)).branch d).apply
    (((instrument f).record.toKraus.seq
      (instrument (fun p : (Space.tensor (.register m) a).Basis => g p.2)).record.toKraus).apply ρ) _ _ = _
  rw [Kraus.seq_apply, test_entry, record_entry (a := .tensor (.register m) a), record_entry (a := a)]


theorem decision_record (f : a.Basis → Fin m) (g : a.Basis → Fin k)
    (P : Fin m → Prop) [DecidablePred P] (ρ : Operator a) :
    (decideBefore f g P).record.toKraus.apply ρ = (decideAfter f g P).record.toKraus.apply ρ :=
  Instrument.record_congr _ _ ρ (fun d => decision_branch f g P d ρ)

end
end Foundation.Quantum.PartitionMeasurement
