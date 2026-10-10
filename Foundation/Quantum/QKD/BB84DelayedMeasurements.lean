import Foundation.Quantum.PartitionDelay
import Foundation.Quantum.QKD.BB84ErrorExperiment

/-! Error-side measurement first, key-side measurement later, for arbitrary
common BB84 basis strings and arbitrary entangled input. This is the local
measurement-order step of Bouman--Fehr §6, Figure 1 (middle/right), not yet
a theorem about independent basis selection and sifting in the full protocol. -/
namespace Foundation.Quantum.QKD.BB84DelayedMeasurements
noncomputable section
open BB84ErrorTransform PartitionMeasurement
set_option backward.isDefEq.respectTransparency false

abbrev jointSpace (n : Nat) (e : Space) := Space.tensor (.tensor (qubits n) (qubits n)) e
abbrev count (n : Nat) := Fintype.card (Fin n → Fin 2)

def errorLabel {n : Nat} (θ : Fin n → BB84Basis) {e : Space} :
    (jointSpace n e).Basis → Fin (count n) :=
  fun p => Fintype.equivFin (Fin n → Fin 2) (errorBits θ p.1)

def keyLabel {n : Nat} (θ : Fin n → BB84Basis) {e : Space} :
    (jointSpace n e).Basis → Fin (count n) :=
  fun p => Fintype.equivFin (Fin n → Fin 2) (keyBits θ p.1)

abbrev outputSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (count n)) (.tensor (.register (count n)) (jointSpace n e))

/-- Only error-side values are recorded; key directions and Eve remain quantum. -/
def first {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :=
  (instrument (errorLabel θ (e := e))).record

def delayed {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :
    Channel (jointSpace n e) (outputSpace n e) :=
  sequential (errorLabel θ) (keyLabel θ)

def joint {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :
    Channel (jointSpace n e) (outputSpace n e) :=
  simultaneous (errorLabel θ) (keyLabel θ)

/-- First measurement preserves every matrix entry inside one error fiber. -/
theorem first_entry {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Operator (jointSpace n e)) (i j : (jointSpace n e).Basis)
    (h : errorLabel θ i = errorLabel θ j) :
    (first θ e).toKraus.apply ρ (errorLabel θ i,i) (errorLabel θ i,j) = ρ i j := by
  change (instrument (errorLabel θ)).record.toKraus.apply ρ _ _ = _
  rw [record_entry (a := jointSpace n e)]
  simp [h]

theorem delayed_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Operator (jointSpace n e)) :
    (delayed θ e).toKraus.apply ρ = (joint θ e).toKraus.apply ρ :=
  sequential_eq _ _ ρ

/-- Consume the coherent operation equality, then delay key-side measurement.
The conclusion includes both classical records and all residual quantum systems. -/
theorem of_coherent {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Operator (jointSpace n e))
    (h : ((original n θ).amplify e).toKraus.apply ρ =
      ((modified n θ).amplify e).toKraus.apply ρ) :
    (delayed θ e).toKraus.apply (((original n θ).amplify e).toKraus.apply ρ) =
      (joint θ e).toKraus.apply (((modified n θ).amplify e).toKraus.apply ρ) := by
  rw [delayed_eq, h]

end
end Foundation.Quantum.QKD.BB84DelayedMeasurements
