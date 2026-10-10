import Foundation.Constructions.Hash.NativeIdealResources
import Foundation.Constructions.Hash.OracleWorlds
import Foundation.Crypto.Semantics.Oracle.RandomOracleReindex

/-! Faithful connection of native bit packets and the typed compression
interface used by the hash security proof. The actual lazy table is reindexed,
not resampled or supplied to the adversary as additional information. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

/-- Fixed-width packet representation of the original compression input. -/
def compressionPacket {n κ : Nat} (input : CompressionInput (Bits κ) (Bits n)) : List Bool :=
  input.1.toList ++ input.2.1 :: input.2.2.toList

/-- Actual packet length includes the chaining value, marker and payload. -/
theorem compressionPacket_length {n κ : Nat} (input : CompressionInput (Bits κ) (Bits n)) :
    (compressionPacket input).length = n + κ + 1 := by
  simp [compressionPacket]
  omega


def compressionKey {n κ : Nat} (input : CompressionInput (Bits κ) (Bits n)) : Bits (n + κ + 1) :=
  ((fixedBits (n + κ + 1)).decode (compressionPacket input)).getD (fun _ => false)

theorem compressionKey_encode {n κ : Nat} (input : CompressionInput (Bits κ) (Bits n)) :
    (fixedBits (n + κ + 1)).encode (compressionKey input) = compressionPacket input := by
  obtain ⟨key, decoded, encoded⟩ := compression_packet_valid n κ input.1 input.2.1 input.2.2
  simpa only [compressionKey, compressionPacket, decoded, Option.getD_some] using encoded

theorem compressionKey_decode {n κ : Nat} (input : CompressionInput (Bits κ) (Bits n)) :
    (fixedBits (n + κ + 1)).decode (compressionPacket input) = some (compressionKey input) := by
  rw [← compressionKey_encode, FiniteBitEncoding.decode_encode]

theorem compressionKey_injective (n κ : Nat) :
    Function.Injective (@compressionKey n κ) := by
  intro left right equal
  have packets := congrArg (fixedBits (n + κ + 1)).encode equal
  rw [compressionKey_encode, compressionKey_encode] at packets
  have take (d : Bits n) (tail : List Bool) : (d.toList ++ tail).take n = d.toList := by
    simpa only [Bits.length_toList] using (List.take_left (l₁ := d.toList) (l₂ := tail))
  have drop (d : Bits n) (tail : List Bool) : (d.toList ++ tail).drop n = tail := by
    simpa only [Bits.length_toList] using (List.drop_left (l₁ := d.toList) (l₂ := tail))
  have first := congrArg (List.take n) packets
  have rest := congrArg (List.drop n) packets
  simp only [compressionPacket, take] at first
  simp only [compressionPacket, drop] at rest
  have firstEq : left.1 = right.1 := List.ofFn_injective first
  have hr : left.2.1 = right.2.1 ∧ left.2.2.toList = right.2.2.toList := List.cons.inj rest
  exact Prod.ext firstEq (Prod.ext hr.1 (List.ofFn_injective hr.2))

def encodeCompressionTable {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) : IdealTable n κ :=
  RandomOracle.mapTable compressionKey table

/-- The concrete native capability agrees with the typed ideal compression
oracle, including its updated table and response encoding. -/
theorem typed_compression_step {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n))
    (input : CompressionInput (Bits κ) (Bits n)) :
    idealCompression n κ (encodeCompressionTable table) (compressionPacket input) =
      (RandomOracle.oracle table input).map (fun answer =>
        (encodeCompressionTable answer.1, answer.2.toList)) := by
  rw [idealCompression, compressionKey_decode]
  simp only [Option.getD_some]
  simp only [encodeCompressionTable]
  rw [← RandomOracle.reindex_step compressionKey (compressionKey_injective n κ) table input]
  simp only [PMF.map_comp, Function.comp_def, fixedBits,
    Foundation.Encoding.vector, Bits.toList]

/-- Encode the final digest, shared state and every typed compression event. -/
def encodeIterationOutcome {Digest Payload Encoded State TargetState : Type}
    (digest : Digest → List Bool) (block : Payload → Encoded) (state : State → TargetState)
    (out : Outcome (Digest × Payload) Digest Digest State) :
    Outcome (List Bool × Encoded) (List Bool) (List Bool) TargetState :=
  ⟨digest out.result, state out.state,
    out.trace.map (fun entry => ((digest entry.1.1, block entry.1.2), digest entry.2))⟩

/-- One-step encoding equality lifts through the existing adaptive iteration.
No inverse decoder or arbitrary native execution law is assumed. -/
theorem iterate_encoded_state_run {Digest Payload Encoded State TargetState : Type}
    (digest : Digest → List Bool) (block : Payload → Encoded) (project : State → TargetState)
    (source : Oracle (Digest × Payload) Digest State)
    (target : Oracle (List Bool × Encoded) (List Bool) TargetState)
    (step : ∀ state previous payload, target (project state) (digest previous, block payload) =
      (source state (previous, payload)).map (fun answer => (project answer.1, digest answer.2)))
    (initial : Digest) (blocks : List Payload) (state : State) :
    ((Foundation.Hash.iterate (digest initial) (blocks.map block)).run target (project state)) =
      ((Foundation.Hash.iterate initial blocks).run source state).map
        (encodeIterationOutcome digest block project) := by
  induction blocks generalizing initial state with
  | nil => simp [Foundation.Hash.iterate, Program.run, encodeIterationOutcome, PMF.pure_map]
  | cons payload rest ih =>
      simp only [List.map_cons, Foundation.Hash.iterate, Program.run, step,
        PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
      congr 1
      funext answer
      rw [ih]
      simp only [PMF.map_comp, Function.comp_def]
      congr 1

end Foundation.Hash.Native
