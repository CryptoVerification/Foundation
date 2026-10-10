import Foundation.Quantum.QKD.BB84OutcomeCoordinates
import Foundation.Quantum.PartitionDiscard
import Foundation.Quantum.ClassicalComposition

/-! Common-basis deferred measurements connected to the existing raw output
format, after physically discarding the signal. Aborted private keys are
absent by RawProtocol.output; the environment remains quantum. -/
namespace Foundation.Quantum.QKD.BB84DeferredRaw
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84OutcomeCoordinates PartitionMeasurement
set_option backward.isDefEq.respectTransparency false

abbrev labelCount (n : Nat) := pairCount (count n) (count n)

def signalLabel {n : Nat} (θ : Fin n → BB84Basis) :
    (signalSpace n).Basis → Fin (labelCount n) :=
  fun p => Fintype.equivFin (Fin (count n) × Fin (count n)) (encode θ p)

def rawLabel {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
    (p : (signalSpace n).Basis) : Fin (Fintype.card (RawProtocol.Output n)) :=
  Fintype.equivFin (RawProtocol.Output n)
    (RawProtocol.output θ θ (readBits p.2) (readBits p.1) T minKey tolerance)

def recoverLabel {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
    (r : Fin (labelCount n)) : Fin (Fintype.card (RawProtocol.Output n)) :=
  rawLabel θ T minKey tolerance (originalOutcomes θ
    ((Fintype.equivFin (Fin (count n) × Fin (count n))).symm r))

theorem recover_signal {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (p : (signalSpace n).Basis) :
    recoverLabel θ T minKey tolerance (signalLabel θ (relabel n θ p)) =
      rawLabel θ T minKey tolerance p := by
  simp only [recoverLabel, signalLabel, Equiv.symm_apply_apply, originalOutcomes_encode]

/-- The same raw output, with both private keys erased on abort. -/
theorem abort_keys {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (r : Fin (labelCount n))
    (h : (((Fintype.equivFin (RawProtocol.Output n)).symm
      (recoverLabel θ T minKey tolerance r)).transcript.accepted) = false) :
    ((Fintype.equivFin (RawProtocol.Output n)).symm
      (recoverLabel θ T minKey tolerance r)).aliceKey = (fun _ => none) ∧
    ((Fintype.equivFin (RawProtocol.Output n)).symm
      (recoverLabel θ T minKey tolerance r)).bobKey = (fun _ => none) := by
  simp only [recoverLabel, rawLabel, Equiv.symm_apply_apply] at h ⊢
  exact RawProtocol.abort_keys _ _ _ _ _ _ _ h

/-- Common-basis measurement without a virtual CNOT, using the existing
raw-output constructor, with the signal traced out and Eve retained. -/
def reference {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (T : Finset (Fin n))
    (minKey tolerance : Nat) :=
  (((BB84ErrorTransform.basisChannel n θ).amplify e).seq
    (FirstRegister.channel (signalSpace n) e)).seq
      (classicalMap e (fun r => rawLabel θ T minKey tolerance
        ((Fintype.equivFin (signalSpace n).Basis).symm r)))

/-- Actual CNOT experiment with error-first and key-later measurements,
followed by signal discard and classical raw-output reconstruction. -/
def deferred {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (T : Finset (Fin n))
    (minKey tolerance : Nat) :=
  (((original n θ).amplify e).seq
    (sequentialDiscard (fun p => (encode θ p).1) (fun p => (encode θ p).2) e)).seq
      (classicalMap e (recoverLabel θ T minKey tolerance))

theorem output_of_coherent {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e))
    (h : ((original n θ).amplify e).toKraus.apply ρ =
      ((modified n θ).amplify e).toKraus.apply ρ) :
    (deferred θ e T minKey tolerance).toKraus.apply ρ =
      (reference θ e T minKey tolerance).toKraus.apply ρ := by
  change (((original n θ).amplify e).toKraus.seq
    (sequentialDiscard (fun p => (encode θ p).1) (fun p => (encode θ p).2) e).toKraus |>.seq
      (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus).apply ρ =
    ((((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.seq
      (FirstRegister.channel (signalSpace n) e).toKraus).seq
        (classicalMap e (fun r => rawLabel θ T minKey tolerance
          ((Fintype.equivFin (signalSpace n).Basis).symm r))).toKraus).apply ρ
  simp only [Kraus.seq_apply]
  rw [sequential_discard_eq, discard_eq, h]
  change (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus.apply
    ((classicalMap e (fun r => signalLabel θ ((Fintype.equivFin (signalSpace n).Basis).symm r))).toKraus.apply
      ((FirstRegister.channel (signalSpace n) e).toKraus.apply
        (((((BB84ErrorTransform.basisChannel n θ).toKraus.seq (relabelChannel n θ).toKraus).amplify e)).apply ρ))) = _
  rw [Kraus.amplify_seq, Kraus.seq_apply]
  dsimp only [relabelChannel]
  have hr := FirstRegister.relabel (signalSpace n) e (relabelEquiv n θ)
    (((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.apply ρ)
  refine (congrArg (fun A => (classicalMap e (recoverLabel θ T minKey tolerance)).toKraus.apply
    ((classicalMap e (fun r => signalLabel θ ((Fintype.equivFin (signalSpace n).Basis).symm r))).toKraus.apply A)) hr).trans ?_
  rw [classicalMap_compose, classicalMap_compose]
  congr 1
  apply congrArg (fun f => (classicalMap e f).toKraus)
  funext r
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  exact recover_signal θ T minKey tolerance _

theorem output_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (deferred θ e T minKey tolerance).toKraus.apply ρ =
      (reference θ e T minKey tolerance).toKraus.apply ρ :=
  output_of_coherent θ T minKey tolerance ρ (amplified n θ e ρ)

/-- Forget the private raw keys, retaining only the existing public transcript
and the complete quantum environment. -/
def publicChannel (n : Nat) (e : Space) :=
  classicalMap e (fun r : Fin (Fintype.card (RawProtocol.Output n)) =>
    Fintype.equivFin (RawProtocol.PublicRecord n)
      (((Fintype.equivFin (RawProtocol.Output n)).symm r).transcript))

theorem public_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (publicChannel n e).toKraus.apply ((deferred θ e T minKey tolerance).toKraus.apply ρ) =
      (publicChannel n e).toKraus.apply ((reference θ e T minKey tolerance).toKraus.apply ρ) :=
  congrArg (publicChannel n e).toKraus.apply (output_eq θ T minKey tolerance ρ)

end
end Foundation.Quantum.QKD.BB84DeferredRaw
