import Foundation.Quantum.QKD.BB84DelayedMeasurements
import Foundation.Quantum.QKD.BB84RawProtocol
import Foundation.Quantum.PartitionDecision

/-! Public acceptance from the error-side record, before measuring the key.
The acceptance predicate agrees with RawProtocol for common bases, including
minimum remaining key length and a nonzero tolerated sample error count. -/
namespace Foundation.Quantum.QKD.BB84DelayedDecision
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements PartitionMeasurement
set_option backward.isDefEq.respectTransparency false

/-- The public test uses only the sampled error bits and the length guard. -/
def accepts {n : Nat} (T : Finset (Fin n)) (minKey tolerance : Nat) (r : Fin (count n)) : Prop :=
  minKey ≤ (Finset.univ \ T).card ∧
    (T.filter (fun i => (Fintype.equivFin (Fin n → Fin 2)).symm r i ≠ 0)).card ≤ tolerance

instance {n : Nat} (T : Finset (Fin n)) (minKey tolerance : Nat) :
    DecidablePred (accepts T minKey tolerance) := fun r => by unfold accepts; infer_instance

theorem raw_accepts {n : Nat} (θ : Fin n → BB84Basis) (b a : (qubits n).Basis)
    {e : Space} (u : e.Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    RawProtocol.accepts θ θ (readBits a) (readBits b) T minKey tolerance =
      decide (accepts T minKey tolerance (errorLabel θ (relabel n θ (b,a),u))) := by
  have hx (x y : Fin 2) : (bitXor x y ≠ 0) ↔ y ≠ x := by
    fin_cases x <;> fin_cases y <;> decide
  have hmatched : RawProtocol.matched θ θ = Finset.univ := by
    simp [RawProtocol.matched]
  simp only [accepts, errorLabel, Equiv.symm_apply_apply, errorBits_relabel]
  simp_rw [hx]
  simp [RawProtocol.accepts, RawProtocol.keyPositions, RawProtocol.errors, hmatched]

def before {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Instrument (jointSpace n e) (outputSpace n e) 2 :=
  decideBefore (errorLabel θ) (keyLabel θ) (accepts T minKey tolerance)

def after {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Instrument (jointSpace n e) (outputSpace n e) 2 :=
  decideAfter (errorLabel θ) (keyLabel θ) (accepts T minKey tolerance)

/-- Both accept and abort outputs agree, before any outcome normalization. -/
theorem branch_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (d : Fin 2) (ρ : Operator (jointSpace n e)) :
    ((before θ e T minKey tolerance).branch d).apply ρ =
      ((after θ e T minKey tolerance).branch d).apply ρ :=
  decision_branch _ _ _ d ρ

theorem record_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (before θ e T minKey tolerance).record.toKraus.apply ρ =
      (after θ e T minKey tolerance).record.toKraus.apply ρ :=
  decision_record _ _ _ ρ

/-- Consume the actual CNOT transformation and retain the public decision. -/
theorem of_coherent {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e))
    (h : ((original n θ).amplify e).toKraus.apply ρ =
      ((modified n θ).amplify e).toKraus.apply ρ) :
    (before θ e T minKey tolerance).record.toKraus.apply
      (((original n θ).amplify e).toKraus.apply ρ) =
    (after θ e T minKey tolerance).record.toKraus.apply
      (((modified n θ).amplify e).toKraus.apply ρ) := by
  rw [record_eq, h]

end
end Foundation.Quantum.QKD.BB84DelayedDecision
