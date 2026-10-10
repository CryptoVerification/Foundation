import Foundation.Constructions.Hash.QueryIndifferentiability
import Foundation.Crypto.Semantics.Oracle.WholeAttack
import Foundation.Crypto.Semantics.Machine.ListEncoding

/-! Real/ideal ROM observations for the existing whole interactive machine.
The same finite code is run against genuinely different opaque state types.
Oracle-boundary codecs and hash evaluation remain challenger operations: this
bridge does not certify native table search, hash iteration or simulator code. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability Machine
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

/-- Existing faithful codecs for lists, products and sums give a canonical
public encoding of the two hash windows. Malformed packets select the empty
high-level message; this convention belongs to the challenger interface. -/
def wholeInterface (initial : Digest) (terminal : Payload)
    (payloadEncoding : FiniteBitEncoding Payload) (digestEncoding : FiniteBitEncoding Digest) :
    WholeInterface (protocol (candidate initial terminal) initial terminal) where
  instanceEncoding _ := FiniteBitEncoding.unit
  requestEncoding := payloadEncoding.list.sum (digestEncoding.prod (FiniteBitEncoding.bool.prod payloadEncoding))
  responseEncoding := digestEncoding
  fallbackRequest := .inl []

/-- Mathematical packet length, without assigning machine costs to encoding. -/
theorem whole_high_packet_length (initial : Digest) (terminal : Payload)
    (payloadEncoding : FiniteBitEncoding Payload) (digestEncoding : FiniteBitEncoding Digest)
    (message : List Payload) :
    ((wholeInterface initial terminal payloadEncoding digestEncoding).requestEncoding.encode (.inl message)).length =
      2 * (message.map (fun block => (payloadEncoding.encode block).length)).sum + 2 * message.length + 2 := by
  simp [wholeInterface, FiniteBitEncoding.sum, FiniteBitEncoding.list, FiniteBitEncoding.encodeList_length]

/-- A low-level packet contains one encoded chaining value, marker and payload. -/
theorem whole_low_packet_length (initial : Digest) (terminal : Payload)
    (payloadEncoding : FiniteBitEncoding Payload) (digestEncoding : FiniteBitEncoding Digest)
    (previous : Digest) (marker : Bool) (block : Payload) :
    ((wholeInterface initial terminal payloadEncoding digestEncoding).requestEncoding.encode
      (.inr (previous, (marker, block)))).length =
      2 * (digestEncoding.encode previous).length + (payloadEncoding.encode block).length + 5 := by
  simp [wholeInterface, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.prod_encode_length,
    FiniteBitEncoding.bool]
  omega

/-- The complete native observations have the proved hash distinguishing
bound whenever this exact finite code realizes the typed bounded interaction.
Stopping and full-state/transcript realization are the existing WholeWitness
obligations; no new realization or machine-time assertion is assumed as a
cryptographic axiom. Oracle-internal computation is not charged to this machine. -/
theorem whole_result_gap (initial : Digest) (terminal : Payload)
    (payloadEncoding : FiniteBitEncoding Payload) (digestEncoding : FiniteBitEncoding Digest)
    (time queries : Nat → Nat)
    (F : InstanceFamily (CryptoOracle.goal (protocol (candidate initial terminal) initial terminal)))
    (A : AdversaryFamily (CryptoOracle.goal (protocol (candidate initial terminal) initial terminal)) F)
    (W : WholeWitness (wholeInterface initial terminal payloadEncoding digestEncoding) time queries F A)
    (n blockLimit : Nat) (bound : WorldBound blockLimit (A n) (queries n)) :
    let J := wholeInterface initial terminal payloadEncoding digestEncoding
    let Q := queries n * blockLimit
    probabilityGap
      (eventProb ((J.execution W.code n (F n) false (time n)).map Interactive.observe)
        (fun out => out.result = some true))
      (eventProb ((J.execution W.code n (F n) true (time n)).map Interactive.observe)
        (fun out => out.result = some true)) ≤
      ((Q * (Q + 1) + (2 * Q * (Q + 1) + queries n * Q) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  dsimp only
  rw [W.realizes n false, W.realizes n true]
  have gap := candidate_gap_bound bound initial terminal (List.finRange (queries n * blockLimit))
    (List.nodup_finRange _) (by simp) initial (fun result => result = true)
  simpa only [eventProb_map, WholeInterface.encodeOutcome, Option.some.injEq, Fintype.card_fin,
    WholeInterface.world, WholeInterface.initialState, protocol, candidate] using gap

end Foundation.Hash
