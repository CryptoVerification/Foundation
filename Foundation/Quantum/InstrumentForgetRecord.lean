import Foundation.Quantum.ClassicalControl
import Foundation.Quantum.RecordObservation

/-! Physical removal of an instrument's explicit classical outcome. This
retains the complete quantum marginal, not a selected normalized branch. -/
namespace Foundation.Quantum.Instrument
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Measure and discard the outcome register, acting identically on output. -/
def forgetRecord (b : Space) (m : Nat) : Channel (.tensor (.register m) b) b :=
  ClassicalControl.channel (fun _ : Fin m => Channel.identity b)

theorem forgetRecord_apply (b : Space) (m : Nat) (ρ : Operator (.tensor (.register m) b)) :
    (forgetRecord b m).toKraus.apply ρ = ∑ r : Fin m, fun i j => ρ (r,i) (r,j) := by
  rw [show forgetRecord b m = ClassicalControl.channel (fun _ : Fin m => Channel.identity b) from rfl,
    ClassicalControl.apply]
  simp [Channel.identity, Channel.ofIsometry, Kraus.single_apply]

theorem forget_record {a b : Space} {m : Nat} (I : Instrument a b m) (ρ : Operator a) :
    (forgetRecord b m).toKraus.apply (I.record.toKraus.apply ρ) = I.forget.toKraus.apply ρ := by
  rw [forgetRecord_apply, I.forget_apply]
  apply Finset.sum_congr rfl
  intro r _
  ext i j
  exact I.record_diagonal ρ r i j

end
end Foundation.Quantum.Instrument
