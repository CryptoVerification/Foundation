import Foundation.Quantum.RetainedControl
import Foundation.Quantum.InstrumentPost

/-! A physical channel after a recorded instrument retains the outcome. -/
namespace Foundation.Quantum.Instrument
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem retained_post {a b c : Space} {m : Nat} (I : Instrument a b m)
    (C : Channel b c) (ρ : Operator a) :
    (RetainedControl.channel (fun _ : Fin m => C)).toKraus.apply (I.record.toKraus.apply ρ) =
      (I.post C).record.toKraus.apply ρ := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [RetainedControl.apply_entry]
  by_cases h : r = s
  · subst s
    simp only [ite_true]
    have hb : Matrix.of (fun u v => I.record.toKraus.apply ρ (r,u) (r,v)) = (I.branch r).apply ρ := by
      ext u v
      exact I.record_diagonal ρ r u v
    rw [hb, Instrument.record_diagonal, post_apply]
  · simp only [h, ite_false]
    simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma, apply_ite, ite_mul, h]

/-- Preprocessing may be evaluated on the input without changing any outcome
or remaining quantum output. -/
theorem record_pre {a b c : Space} {m : Nat} (I : Instrument b c m)
    (C : Channel a b) (ρ : Operator a) :
    (I.pre C).record.toKraus.apply ρ = I.record.toKraus.apply (C.toKraus.apply ρ) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · subst s
    rw [Instrument.record_diagonal, Instrument.record_diagonal, pre_apply]
  · simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma, apply_ite, ite_mul, h]

end
end Foundation.Quantum.Instrument
