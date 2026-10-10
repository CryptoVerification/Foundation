import Foundation.Quantum.QKD.RawReconciliation
import Foundation.Quantum.QKD.BB84SiftedOutput

/-! The actual full-position decoder uses only the original public bases,
test set, Alice's public parity/suffix record and Bob's local raw key.
No sampling-certificate configuration is supplied to this algorithm. -/
namespace Foundation.Quantum.QKD.FullRawReconciliation
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

def restrictKey {n : Nat} (M : Finset (Fin n)) (key : Finalization.RawKey n) :
    Finalization.RawKey (BB84SiftedInput.selectedCount M) :=
  fun j => key (BB84SiftedInput.indexEmbedding M j)

theorem restrict_expand {n : Nat} (M : Finset (Fin n))
    (key : Finalization.RawKey (BB84SiftedInput.selectedCount M)) :
    restrictKey M (BB84SiftedInput.expand M key) = key := by
  funext j
  exact BB84SiftedInput.expand_index M key j

abbrev selected {n : Nat} (p : RawProtocol.PublicRecord n) :=
  RawProtocol.matched p.aliceBases p.bobBases

abbrev tested {n : Nat} (p : RawProtocol.PublicRecord n) :=
  BB84SiftedInput.restrictTest (selected p) p.tested

def localMessage {n : Nat} (M : Finset (Fin n)) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (alice : Finalization.RawKey n) :=
  ArbitraryReconciliation.quantumMessage (RawReconciliation.remaining T (restrictKey M alice))

def localBob {n : Nat} (M : Finset (Fin n)) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (bob : Finalization.RawKey n) (msg : ArbitraryReconciliation.Message (BB84SiftedInput.remainderCount T)) :
    Finalization.RawKey n :=
  BB84SiftedInput.expand M (optionalKey T
    (ArbitraryReconciliation.quantumDecode (RawReconciliation.remaining T (restrictKey M bob)) msg))

def packedMessage {n : Nat} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (alice : Finalization.RawKey n) :
    ArbitraryReconciliation.Word n :=
  ArbitraryReconciliation.messageRecord (RawReconciliation.public_fits M T) (localMessage M T alice)

def publicMessage {n : Nat} (o : RawProtocol.Output n) : ArbitraryReconciliation.Word n :=
  packedMessage (selected o.transcript) (tested o.transcript) o.aliceKey

def decodeRecord {n : Nat} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (bob : Finalization.RawKey n)
    (record : ArbitraryReconciliation.Word n) : Finalization.RawKey n :=
  localBob M T bob (ArbitraryReconciliation.messageFromRecord (RawReconciliation.public_fits M T) record)

/-- Bob reconstructs the entire decoder message from the actual public record. -/
def bobKey {n : Nat} (p : RawProtocol.PublicRecord n) (bob : Finalization.RawKey n)
    (record : ArbitraryReconciliation.Word n) : Finalization.RawKey n :=
  decodeRecord (selected p) (tested p) bob record

def output {n : Nat} (o : RawProtocol.Output n) : RawProtocol.Output n :=
  ⟨o.transcript,o.aliceKey,bobKey o.transcript o.bobKey (publicMessage o)⟩

theorem selected_restore {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) :
    selected (BB84SiftedInput.restoreOutput M θ o).transcript = M :=
  BB84SiftingRandomness.matched_bob θ M

/-- The padded record contains exactly the small raw decoder's message. -/
theorem publicMessage_restore {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) :
    publicMessage (BB84SiftedInput.restoreOutput M θ o) =
      RawReconciliation.publicMessage M o.transcript.tested o := by
  dsimp only [publicMessage, tested, selected, BB84SiftedInput.restoreOutput]
  rw [BB84SiftingRandomness.matched_bob, BB84SiftedInput.restrict_lift]
  simp only [packedMessage, localMessage, restrict_expand,
    RawReconciliation.publicMessage, RawReconciliation.message]

/-- Exact original-position corrected key; no assumption of successful
error correction is needed for this identity of specified algorithms. -/
theorem bobKey_restore {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) :
    (output (BB84SiftedInput.restoreOutput M θ o)).bobKey =
      BB84SiftedInput.expand M (RawReconciliation.bobKey o.transcript.tested o) := by
  unfold output
  rw [publicMessage_restore]
  dsimp only [bobKey, tested, selected, BB84SiftedInput.restoreOutput]
  rw [BB84SiftingRandomness.matched_bob, BB84SiftedInput.restrict_lift]
  simp only [decodeRecord, RawReconciliation.publicMessage, ArbitraryReconciliation.message_roundtrip,
    localBob, restrict_expand, RawReconciliation.bobKey]

end
end Foundation.Quantum.QKD.FullRawReconciliation
