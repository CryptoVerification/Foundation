import Foundation.Quantum.QKD.PairwiseRecoveryExamples
import Foundation.Quantum.QKD.BB84SiftedFullRecord

/-! Actual key measurement and raw-output reconstruction after the retained
first error measurement. Acceptance and abort key erasure are the existing
BB84 constructors, and both branches remain normalized together. -/
namespace Foundation.Quantum.QKD.PairwiseRawPost
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84PairwiseReference PartitionMeasurement
set_option backward.isDefEq.respectTransparency false

/-- Measure the key coordinates, discard the signal, and construct the raw
output with the test-dependent acceptance flag and absent keys on abort. -/
def afterFirst {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (T : Finset (Fin n))
    (minKey tolerance : Nat) :=
  (instrument (fun p : (Space.tensor (.register (count n)) (jointSpace n e)).Basis =>
    keyLabel θ p.2)).record.seq (BB84DecisionRaw.finish θ e T minKey tolerance)

theorem after_first_deferred {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (afterFirst θ e T minKey tolerance).toKraus.apply
      ((actualFirst θ e).record.toKraus.apply ρ) =
      (BB84DeferredRaw.deferred θ e T minKey tolerance).toKraus.apply ρ := by
  rw [actualFirst, Instrument.record_pre]
  simp only [afterFirst, BB84DecisionRaw.finish, BB84DeferredRaw.deferred,
    sequentialDiscard, sequential, Channel.seq, Kraus.seq_apply]
  rfl

/-- Equality with the existing physical experiment that decides before the
key measurement. No conditioning by the acceptance probability occurs. -/
theorem after_first_decided {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (afterFirst θ e T minKey tolerance).toKraus.apply
      ((actualFirst θ e).record.toKraus.apply ρ) =
      (BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply ρ :=
  (after_first_deferred θ e T minKey tolerance ρ).trans
    (BB84DecisionRaw.decided_deferred θ T minKey tolerance ρ).symm

theorem after_first_reference {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (afterFirst θ e T minKey tolerance).toKraus.apply
      ((actualFirst θ e).record.toKraus.apply ρ) =
      (BB84DeferredRaw.reference θ e T minKey tolerance).toKraus.apply ρ :=
  (after_first_deferred θ e T minKey tolerance ρ).trans
    (BB84DeferredRaw.output_eq θ T minKey tolerance ρ)

theorem joined_bases {n : Nat} (M : Finset (Fin n))
    (θ : Fin (BB84SiftedInput.selectedCount M) → BB84Basis)
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) :
    BB84SiftedInput.bases M (BB84SiftedInput.joinBases M (θ,η)) = θ := by
  funext i
  simp [BB84SiftedInput.bases, BB84SiftedInput.joinBases]

/-- Reconstruct original positions and full bases, and discard only unmatched
signals. The original Eve system and both actual private raw keys remain. -/
def restore {n : Nat} (M : Finset (Fin n))
    (θ : Fin (BB84SiftedInput.selectedCount M) → BB84Basis)
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (e : Space)
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (minKey tolerance : Nat) :=
  (afterFirst θ (BB84SiftedInput.auxiliary M e) T minKey tolerance).seq
    (BB84SiftedInput.finish M (BB84SiftedInput.joinBases M (θ,η)) e)

/-- The same concrete postprocessing equals the actual uniformly prepared
BB84 record, with original positions, test set, acceptance and abort erasure. -/
theorem restored_prepared {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin (BB84SiftedInput.selectedCount M) → BB84Basis)
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (minKey tolerance : Nat) :
    (restore M θ η e T minKey tolerance).toKraus.apply
      ((actualFirst θ (BB84SiftedInput.auxiliary M e)).record.toKraus.apply (BB84SiftedInput.input A M).matrix) =
      (BB84MixedPreparedRaw.prepared A (BB84SiftedInput.joinBases M (θ,η))
        (BB84SiftingRandomness.bobBases (BB84SiftedInput.joinBases M (θ,η)) M)
        (BB84SiftedInput.liftTest M T) minKey tolerance).matrix := by
  have h := BB84SiftedInput.delayed_prepared A M (BB84SiftedInput.joinBases M (θ,η))
    T minKey tolerance
  simp only [BB84SiftedInput.delayedOutput, joined_bases, Channel.seq, Kraus.seq_apply] at h
  simp only [restore, Channel.seq, Kraus.seq_apply]
  rw [after_first_decided]
  exact h

end
end Foundation.Quantum.QKD.PairwiseRawPost
