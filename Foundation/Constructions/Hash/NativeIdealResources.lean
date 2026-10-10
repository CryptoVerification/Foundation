import Foundation.Constructions.Hash.NativeHash
import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Oracle.EncodedStorage
import Foundation.Crypto.Semantics.Machine.ListEncoding

/-! Concrete ideal compression capability and complete encoded-space bounds
for specialized native hash execution. Compression has a finite fixed-width
input alphabet and n-bit uniformly sampled outputs. Invalid bit packets use
an explicit fallback key. Table lookup, sampling and decoding remain challenger
operations; only native control/transfer time is charged by this machine. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def fixedBits (width : Nat) : FiniteBitEncoding (Bits width) where
  encode := (Foundation.Encoding.vector Bool width).encode
  decode := (Foundation.Encoding.vector Bool width).decode
  decode_encode := (Foundation.Encoding.vector Bool width).roundtrip

@[simp] theorem fixedBits_length (width : Nat) (value : Bits width) :
    ((fixedBits width).encode value).length = width := by
  simp [fixedBits, Foundation.Encoding.vector]

/-- Every packet of the exact public width decodes faithfully. Consequently
valid compression packets never select the malformed-input fallback. -/
theorem fixedBits_decode_exists (width : Nat) (raw : List Bool) (length : raw.length = width) :
    ∃ value : Bits width, (fixedBits width).decode raw = some value ∧
      (fixedBits width).encode value = raw := by
  subst width
  refine ⟨fun i => raw[i.val], ?_, ?_⟩
  · simp [fixedBits, Foundation.Encoding.vector]
  · exact List.ofFn_getElem

theorem compression_packet_valid (digestWidth payloadWidth : Nat)
    (digest : Bits digestWidth) (marker : Bool) (payload : Bits payloadWidth) :
    ∃ key : Bits (digestWidth + payloadWidth + 1),
      (fixedBits (digestWidth + payloadWidth + 1)).decode
        (digest.toList ++ marker :: payload.toList) = some key ∧
      (fixedBits (digestWidth + payloadWidth + 1)).encode key =
        digest.toList ++ marker :: payload.toList :=
  fixedBits_decode_exists _ _ (by simp; omega)

abbrev IdealTable (digestWidth payloadWidth : Nat) :=
  RandomOracle.Table (Bits (digestWidth + payloadWidth + 1)) (Bits digestWidth)

def tableEncoding (digestWidth payloadWidth : Nat) :
    FiniteBitEncoding (IdealTable digestWidth payloadWidth) :=
  ((fixedBits (digestWidth + payloadWidth + 1)).prod (fixedBits digestWidth)).list

def entryIncrement (digestWidth payloadWidth : Nat) : Nat :=
  4 * (digestWidth + payloadWidth + 1) + 2 * digestWidth + 4

def tableSize (digestWidth payloadWidth : Nat) (table : IdealTable digestWidth payloadWidth) : Nat :=
  entryIncrement digestWidth payloadWidth * table.length + 1

theorem tableEncoding_length (digestWidth payloadWidth : Nat) (table : IdealTable digestWidth payloadWidth) :
    ((tableEncoding digestWidth payloadWidth).encode table).length =
      tableSize digestWidth payloadWidth table := by
  induction table with
  | nil => simp [tableEncoding, FiniteBitEncoding.list, FiniteBitEncoding.encodeList, tableSize]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      rw [tableEncoding, FiniteBitEncoding.list_encode_cons_length]
      change _ + ((tableEncoding digestWidth payloadWidth).encode rest).length = _
      rw [ih]
      simp [FiniteBitEncoding.prod_encode_length, tableSize, entryIncrement, Nat.mul_add]
      omega

/-- Exactly the finite-table lazy oracle, followed by its faithful response
encoding. The fallback handles malformed packets; it does not reprogram a key. -/
noncomputable def idealCompression (digestWidth payloadWidth : Nat) :
    BitOracle (IdealTable digestWidth payloadWidth) :=
  fun table request =>
    (RandomOracle.oracle table (((fixedBits (digestWidth + payloadWidth + 1)).decode request).getD
      (fun _ => false))).map (fun answer => (answer.1, (fixedBits digestWidth).encode answer.2))

theorem idealCompression_growth (digestWidth payloadWidth : Nat)
    (table : IdealTable digestWidth payloadWidth) (request : List Bool)
    (answer : IdealTable digestWidth payloadWidth × List Bool)
    (support : answer ∈ (idealCompression digestWidth payloadWidth table request).support) :
    tableSize digestWidth payloadWidth answer.1 ≤
      tableSize digestWidth payloadWidth table + entryIncrement digestWidth payloadWidth ∧
    answer.2.length = digestWidth := by
  rw [idealCompression, PMF.mem_support_map_iff] at support
  obtain ⟨typed, hTyped, rfl⟩ := support
  have h := (RandomOracle.step table _ typed hTyped).2.2
  constructor
  · have hm := Nat.mul_le_mul_left (entryIncrement digestWidth payloadWidth) h
    simp only [Nat.mul_add, Nat.mul_one] at hm
    simp only [tableSize]
    omega
  · exact fixedBits_length digestWidth typed.2

/-- Native correctness is instantiated with an actual ideal compression
oracle; fixed response width is proved from its sampling/encoding semantics. -/
theorem ideal_prefixFree_run (digestWidth payloadWidth : Nat)
    (initial : Bits digestWidth) (terminal : Bits payloadWidth)
    (message : List (Bits payloadWidth)) (input : List Bool)
    (table : IdealTable digestWidth payloadWidth) :
    Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression digestWidth payloadWidth)
      (3 * digestWidth + (message.length + 1) * (7 * digestWidth + 5 * payloadWidth + 11) + 1)
      (Configuration.initial table input) =
    ((Foundation.Hash.prefixFreeMD initial.toList terminal.toList (message.map Bits.toList)).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id
        (idealCompression digestWidth payloadWidth)) table).map
      (hashFinish ((prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)).length - 1)
        (Tape.ofBits input)) := by
  have h := prefixFree_run (idealCompression digestWidth payloadWidth)
    initial.toList terminal.toList (message.map Bits.toList) input table
    (fun state request answer ha => by
      simpa using (idealCompression_growth digestWidth payloadWidth state request answer ha).2)
  rw [prefixFree_steps initial.toList terminal.toList (message.map Bits.toList) payloadWidth
    (by simp) (by intro block hb; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb; simp)] at h
  simpa using h

/-- Actual stopping, with the same concrete budget used by the realization. -/
theorem ideal_prefixFree_halts (digestWidth payloadWidth : Nat)
    (initial : Bits digestWidth) (terminal : Bits payloadWidth)
    (message : List (Bits payloadWidth)) (input : List Bool)
    (table : IdealTable digestWidth payloadWidth) :
    Reification.HaltsWithin
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression digestWidth payloadWidth) (Configuration.initial table input)
      (3 * digestWidth + (message.length + 1) * (7 * digestWidth + 5 * payloadWidth + 11) + 1) := by
  intro finish hFinish
  rw [ideal_prefixFree_run digestWidth payloadWidth initial terminal message input table,
    PMF.mem_support_map_iff] at hFinish
  obtain ⟨out, _, rfl⟩ := hFinish
  rfl

/-- At every supported intermediate transition, bound the faithful encoding
of code, control, all tapes, transfer buffers, full trace and ideal table.
This measures represented bit lengths, not operating-system memory usage. -/
theorem ideal_prefixFree_encoded_peak (digestWidth payloadWidth : Nat)
    (initial : Bits digestWidth) (terminal : Bits payloadWidth)
    (message : List (Bits payloadWidth)) (input : List Bool)
    (table : IdealTable digestWidth payloadWidth) (elapsed : Nat)
    (within : elapsed ≤ 3 * digestWidth + (message.length + 1) *
      (7 * digestWidth + 5 * payloadWidth + 11) + 1)
    (target : Configuration (IdealTable digestWidth payloadWidth))
    (support : target ∈ (Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression digestWidth payloadWidth) elapsed (Configuration.initial table input)).support) :
    (EncodedStorage.codeEncoding.encode
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))).length +
      ((ConfigurationEncoding.frame (tableEncoding digestWidth payloadWidth)).encode target).length ≤
    EncodedStorage.bound
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) 0
      (ControllerExtent.frameExtent (tableSize digestWidth payloadWidth) (Configuration.initial table input))
      (3 * digestWidth + (message.length + 1) * (7 * digestWidth + 5 * payloadWidth + 11) + 1)
      (entryIncrement digestWidth payloadWidth) digestWidth := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding digestWidth payloadWidth)
    (tableSize digestWidth payloadWidth) (fun state => (tableEncoding_length _ _ state).le)
    _ _ (entryIncrement digestWidth payloadWidth) digestWidth
    (fun state request answer ha => by
      have h := idealCompression_growth digestWidth payloadWidth state request answer ha
      exact ⟨h.1, h.2.le⟩)
    _ elapsed within (Configuration.initial table input) target support

end Foundation.Hash.Native
