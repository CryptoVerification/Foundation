import Foundation.Quantum.QKD.PairwiseReconciledCoordinates
import Foundation.Quantum.QKD.ReconciliationMessageRecord

/-! The concrete decoder directly on actual optional-position raw keys.
Absent positions are not quantum resources and are not copied. On the actual
accepted BB84 outputs, extraction exactly inverts the proved remaining-key map. -/
namespace Foundation.Quantum.QKD.RawReconciliation
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

def remaining {m : Nat} (T : Finset (Fin m)) (key : Finalization.RawKey m) :
    (qubits (BB84SiftedInput.remainderCount T)).Basis :=
  writeBits _ (fun j => (key (BB84SiftedInput.remainderIndex T j).val).getD 0)

theorem remaining_optional {m : Nat} (T : Finset (Fin m))
    (x : (qubits (BB84SiftedInput.remainderCount T)).Basis) : remaining T (optionalKey T x) = x := by
  unfold remaining
  have h : (fun j => ((optionalKey T x) (BB84SiftedInput.remainderIndex T j).val).getD 0) = readBits x := by
    funext j
    have hj : (BB84SiftedInput.remainderIndex T).symm
        ⟨(BB84SiftedInput.remainderIndex T j).val, (BB84SiftedInput.remainderIndex T j).property⟩ = j :=
      (BB84SiftedInput.remainderIndex T).symm_apply_apply j
    simp only [optionalKey, (BB84SiftedInput.remainderIndex T j).property,
      dite_false, hj, Option.getD_some]
  rw [h]
  exact write_read _ x

def message {m : Nat} (T : Finset (Fin m)) (o : RawProtocol.Output m) :=
  ArbitraryReconciliation.quantumMessage (remaining T o.aliceKey)

def bobKey {m : Nat} (T : Finset (Fin m)) (o : RawProtocol.Output m) :=
  optionalKey T (ArbitraryReconciliation.quantumDecode (remaining T o.bobKey) (message T o))

/-- Bob's local corrected key uses only his own key and Alice's public message. -/
def output {m : Nat} (T : Finset (Fin m)) (o : RawProtocol.Output m) : RawProtocol.Output m :=
  ⟨o.transcript,o.aliceKey,bobKey T o⟩

theorem public_fits {n : Nat} (M : Finset (Fin n)) (T : Finset (Fin (BB84SiftedInput.selectedCount M))) :
    ArbitraryReconciliation.publicBits (BB84SiftedInput.remainderCount T) ≤ n := by
  have hbits := ArbitraryReconciliation.publicBits_add_blocks (BB84SiftedInput.remainderCount T)
  have hrem : BB84SiftedInput.remainderCount T ≤ BB84SiftedInput.selectedCount M := by
    simpa only [BB84SiftedInput.remainderCount, Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin (BB84SiftedInput.selectedCount M) => i ∉ T)
  have hsel : BB84SiftedInput.selectedCount M ≤ n := by
    simpa only [BB84SiftedInput.selectedCount, Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => i ∈ M)
  omega

def publicMessage {n : Nat} (M : Finset (Fin n)) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) : ArbitraryReconciliation.Word n :=
  ArbitraryReconciliation.messageRecord (public_fits M T) (message T o)

/-- Bob can recover his entire decoder input from the specified public record. -/
theorem bobKey_public {n : Nat} (M : Finset (Fin n)) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) :
    bobKey T o = optionalKey T (ArbitraryReconciliation.quantumDecode (remaining T o.bobKey)
      (ArbitraryReconciliation.messageFromRecord (public_fits M T) (publicMessage M T o))) := by
  rw [publicMessage, ArbitraryReconciliation.message_roundtrip]
  rfl

theorem coordinate_message {m : Nat} (c : PairwiseSampling.Configuration m)
    (minKey tolerance : Nat) (x r : (qubits m).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    message c.2 (coordinateRaw c minKey tolerance (x,r)) =
      ArbitraryReconciliation.quantumMessage (testEquiv c.2 x).1 := by
  unfold message
  rw [coordinate_alice_key c minKey tolerance x r hr, remaining_optional]

theorem coordinate_bobKey {m : Nat} (c : PairwiseSampling.Configuration m)
    (minKey tolerance : Nat) (x r : (qubits m).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    bobKey c.2 (coordinateRaw c minKey tolerance (x,r)) =
      optionalKey c.2 (testEquiv c.2 (PairwiseReconciledVerification.correctedBob c x (bobCoordinate c x r))).1 := by
  unfold bobKey
  rw [coordinate_bob_key c minKey tolerance x r hr, remaining_optional, coordinate_message c minKey tolerance x r hr,
    PairwiseReconciledVerification.correctedBob_remaining]

theorem coordinate_verification {n tag : Nat} (M : Finset (Fin n))
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (minKey tolerance : Nat) (x r : (qubits (BB84SiftedInput.selectedCount M)).Basis)
    (s : Hashing.RawSeed n tag)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (PairwiseExpandedVerification.verificationHash M c s x =
      PairwiseExpandedVerification.verificationHash M c s
        (PairwiseReconciledVerification.correctedBob c x (bobCoordinate c x r))) ↔
      Hashing.rawHash s (BB84SiftedInput.expand M (output c.2 (coordinateRaw c minKey tolerance (x,r))).aliceKey) =
        Hashing.rawHash s (BB84SiftedInput.expand M (output c.2 (coordinateRaw c minKey tolerance (x,r))).bobKey) := by
  change _ ↔ Hashing.rawHash s (BB84SiftedInput.expand M (coordinateRaw c minKey tolerance (x,r)).aliceKey) =
    Hashing.rawHash s (BB84SiftedInput.expand M (bobKey c.2 (coordinateRaw c minKey tolerance (x,r))))
  rw [coordinate_alice_key c minKey tolerance x r hr, coordinate_bobKey c minKey tolerance x r hr]
  rfl

end
end Foundation.Quantum.QKD.RawReconciliation
