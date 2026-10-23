import Foundation.Constructions.Hash.NativeCompactMACObservation

/-! The native backend's key and response alphabets encode the SAME
8-message/256-tag lazy random function, including every cache update. -/
namespace Foundation.Hash.Native.CompactMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

abbrev TypedTable := RandomOracle.Table Message Tag

def encodeTable (table : TypedTable) : Table :=
  table.map (fun entry => (Backend.key entry.1, Backend.tagBits entry.2))

theorem lookup_encodeTable (table : TypedTable) (message : Message) :
    (encodeTable table).lookup (Backend.key message) = (table.lookup message).map Backend.tagBits := by
  induction table with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨key, tag⟩ := entry
      simp only [encodeTable, List.map_cons, List.lookup_cons]
      have same : (Backend.key message == Backend.key key) = (message == key) := by
        by_cases h : message = key
        · subst key; simp
        · simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Backend.key_injective.ne h)]
      rw [same]
      split <;> simp_all [encodeTable]

/-- Cache hits and fresh sampling commute with the actual key/tag codecs. -/
theorem decodedOracle_step (table : TypedTable) (message : Message) :
    decodedOracle (encodeTable table) message =
      (RandomOracle.oracle table message).map (fun answer => (encodeTable answer.1, answer.2)) := by
  have keys : (instBEqProd : BEq (PolygraphOracle.Key 8 0)) =
      (@instBEqOfDecidableEq (PolygraphOracle.Key 8 0) inferInstance) := lawful_beq_subsingleton _ _
  have messages : (inferInstance : BEq Message) =
      (@instBEqOfDecidableEq Message inferInstance) := lawful_beq_subsingleton _ _
  have lookup : @List.lookup (PolygraphOracle.Key 8 0) (Bits 8) instBEqOfDecidableEq
      (Backend.key message) (encodeTable table) =
      (@List.lookup Message Tag instBEqOfDecidableEq message table).map Backend.tagBits := by
    have original := lookup_encodeTable table message
    rw [keys] at original
    simpa only [messages] using original
  simp only [decodedOracle, RandomOracle.oracle, lookup]
  cases found : @List.lookup Message Tag instBEqOfDecidableEq message table with
  | some tag => simp [PMF.pure_map, Backend.decode_tagBits]
  | none =>
      simp only [Option.map_none, PMF.map_comp, Function.comp_def]
      rw [← Backend.uniform_decoded, PMF.map_comp]
      simp only [Function.comp_def, encodeTable, List.map_cons, Backend.tagBits_decode]

/-- Encoding holds for arbitrary adaptive programs, preserving the final
cache, result and complete typed transcript. -/
theorem decodedOracle_run {Result : Type} (program : Program Message Tag Result) (table : TypedTable) :
    (program.run RandomOracle.oracle table).map (Program.mapState encodeTable) =
      program.run decodedOracle (encodeTable table) := by
  apply Program.run_state_map
  intro current message
  exact (decodedOracle_step current message).symm

end Foundation.Hash.Native.CompactMACExecution
