import Foundation.Quantum.QKD.BB84DeferredRaw
import Foundation.Quantum.PartitionDecisionForget

/-! One physical common-basis experiment: error record, explicit public
decision, later key measurement, removal of the duplicate decision register,
signal discard, and the existing raw output with abort keys erased. -/
namespace Foundation.Quantum.QKD.BB84DecisionRaw
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84OutcomeCoordinates BB84DeferredRaw
open PartitionMeasurement
set_option backward.isDefEq.respectTransparency false

/-- The acceptance flag in the recovered raw output is exactly the decision
made from the error label, for every possible pair of classical labels. -/
theorem recovered_acceptance {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (r s : Fin (count n)) :
    (((Fintype.equivFin (RawProtocol.Output n)).symm
      (recoverLabel θ T minKey tolerance (Fintype.equivFin (Fin (count n) × Fin (count n)) (r,s)))).transcript.accepted) =
        decide (BB84DelayedDecision.accepts T minKey tolerance r) := by
  have he : errorLabel θ (e := .unit) (relabel n θ (originalOutcomes θ (r,s)), (():Space.unit.Basis)) = r := by
    change (encode θ (relabel n θ (originalOutcomes θ (r,s)))).1 = r
    simp only [originalOutcomes, relabel_involution]
    exact congrArg Prod.fst (encode_decode θ (r,s))
  have h := BB84DelayedDecision.raw_accepts θ
    (originalOutcomes θ (r,s)).1 (originalOutcomes θ (r,s)).2
    (e := .unit) () T minKey tolerance
  rw [he] at h
  simpa only [recoverLabel, rawLabel, Equiv.symm_apply_apply, RawProtocol.output] using h

/-- Flatten the error/key labels, trace out the signals, and reconstruct only
the existing raw record. The complete adversarial quantum system is retained. -/
def finish {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (T : Finset (Fin n))
    (minKey tolerance : Nat) :=
  ((BasisChannel.channel (reorder (jointSpace n e) (count n) (count n)).symm).seq
    (discardMiddle (.register (labelCount n)) (signalSpace n) e)).seq
      (classicalMap e (recoverLabel θ T minKey tolerance))

def decided {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (T : Finset (Fin n))
    (minKey tolerance : Nat) :=
  ((((original n θ).amplify e).seq (BB84DelayedDecision.before θ e T minKey tolerance).record).seq
    (Instrument.forgetRecord (outputSpace n e) 2)).seq (finish θ e T minKey tolerance)

theorem decided_deferred {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (decided θ e T minKey tolerance).toKraus.apply ρ =
      (deferred θ e T minKey tolerance).toKraus.apply ρ := by
  change (((((original n θ).amplify e).toKraus.seq
    (BB84DelayedDecision.before θ e T minKey tolerance).record.toKraus).seq
      (Instrument.forgetRecord (outputSpace n e) 2).toKraus).seq
        (finish θ e T minKey tolerance).toKraus).apply ρ =
    ((((original n θ).amplify e).toKraus.seq
      (sequentialDiscard (fun p => (encode θ p).1) (fun p => (encode θ p).2) e).toKraus).seq
        (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus).apply ρ
  simp only [Kraus.seq_apply]
  have hd := decision_record_forget (errorLabel θ (e := e)) (keyLabel θ)
    (BB84DelayedDecision.accepts T minKey tolerance)
    (((original n θ).amplify e).toKraus.apply ρ)
  change (finish θ e T minKey tolerance).toKraus.apply
    ((Instrument.forgetRecord (outputSpace n e) 2).toKraus.apply
      ((decideBefore (errorLabel θ) (keyLabel θ) (BB84DelayedDecision.accepts T minKey tolerance)).record.toKraus.apply
        (((original n θ).amplify e).toKraus.apply ρ))) = _
  rw [hd]
  change (((BasisChannel.channel (reorder (jointSpace n e) (count n) (count n)).symm).toKraus.seq
    (discardMiddle (.register (labelCount n)) (signalSpace n) e).toKraus).seq
      (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus).apply
      ((sequential (errorLabel θ) (keyLabel θ)).toKraus.apply
        (((original n θ).amplify e).toKraus.apply ρ)) = _
  simp only [Kraus.seq_apply]
  change _ = (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus.apply
    ((((sequential (errorLabel θ) (keyLabel θ)).toKraus.seq
      (BasisChannel.channel (reorder (jointSpace n e) (count n) (count n)).symm).toKraus).seq
        (discardMiddle (.register (labelCount n)) (signalSpace n) e).toKraus).apply
          (((original n θ).amplify e).toKraus.apply ρ))
  simp only [Kraus.seq_apply]

theorem output_of_coherent {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e))
    (h : ((original n θ).amplify e).toKraus.apply ρ =
      ((modified n θ).amplify e).toKraus.apply ρ) :
    (decided θ e T minKey tolerance).toKraus.apply ρ =
      (reference θ e T minKey tolerance).toKraus.apply ρ :=
  (decided_deferred θ T minKey tolerance ρ).trans
    (BB84DeferredRaw.output_of_coherent θ T minKey tolerance ρ h)

theorem output_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (decided θ e T minKey tolerance).toKraus.apply ρ =
      (reference θ e T minKey tolerance).toKraus.apply ρ :=
  output_of_coherent θ T minKey tolerance ρ (amplified n θ e ρ)

theorem public_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (publicChannel n e).toKraus.apply ((decided θ e T minKey tolerance).toKraus.apply ρ) =
      (publicChannel n e).toKraus.apply ((reference θ e T minKey tolerance).toKraus.apply ρ) :=
  congrArg (publicChannel n e).toKraus.apply (output_eq θ T minKey tolerance ρ)

end
end Foundation.Quantum.QKD.BB84DecisionRaw
