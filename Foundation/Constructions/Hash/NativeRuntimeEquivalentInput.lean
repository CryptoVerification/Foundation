import Foundation.Constructions.Hash.NativeRuntimeTransfer
import Foundation.Crypto.Semantics.Oracle.CellEquivalence

/-! Hashing from the actual cell-equivalent transfer exit. All redundant
 blanks remain in the physical execution. Resuming at the hash entry is
 an interface condition here, not a free machine instruction or a proof of
 combined code linking. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The observed packet, cache and complete transcript realize the typed
hash even when the physical entry has redundant outer blank cells. -/
theorem typed_runtime_equivalent_packet {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (entry : machine.Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList)))) :
    (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (NativeCode.frame (encodeCompressionTable table) prior machine)).map CellEquivalence.packetObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  have law := CellEquivalence.eval_map (runtimeHashCode initial.toList terminal.toList)
    (idealCompression n κ) (runtimeHashSteps n κ message.length)
    (NativeCode.frame (encodeCompressionTable table) prior machine)
    (NativeCode.frame (encodeCompressionTable table) prior
      (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))
    ⟨rfl, rfl, .running entry⟩ CellEquivalence.packetObservation CellEquivalence.packet_eq
  rw [law]
  rw [CellEquivalence.eval_appendTrace]
  change ((Reification.eval _ _ _ (Configuration.initial (encodeCompressionTable table) _)).map _).map _ = _
  rw [typed_runtime_prefixFree_run]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext out
  simp [CellEquivalence.packetObservation, CellEquivalence.appendTrace,
    typedHashFinish, Reification.packet, Machine.Configuration.outputBits, loaded_bits, NativeCode.frame]

/-- The same upper stopping budget holds on every actual physical branch. -/
theorem typed_runtime_equivalent_halts {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (entry : machine.Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList)))) :
    Reification.HaltsWithin (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (NativeCode.frame (encodeCompressionTable table) prior machine)
      (runtimeHashSteps n κ message.length) := by
  have law := CellEquivalence.eval_map (runtimeHashCode initial.toList terminal.toList)
    (idealCompression n κ) (runtimeHashSteps n κ message.length)
    (NativeCode.frame (encodeCompressionTable table) prior machine)
    (NativeCode.frame (encodeCompressionTable table) prior
      (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))
    ⟨rfl, rfl, .running entry⟩ (fun c => Reification.terminal c.control)
    (fun _ _ h => CellEquivalence.terminal h.2.2)
  simp only [NativeCode.frame] at law
  rw [CellEquivalence.eval_appendTrace (runtimeHashCode initial.toList terminal.toList)
    (idealCompression n κ) (runtimeHashSteps n κ message.length) (encodeCompressionTable table)
    (.running (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList)))) prior] at law
  change _ = ((Reification.eval _ _ _ (Configuration.initial (encodeCompressionTable table) _)).map _).map _ at law
  rw [typed_runtime_prefixFree_run] at law
  intro finish support
  have seen : Reification.terminal finish.control ∈
      ((Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
        (runtimeHashSteps n κ message.length)
        (NativeCode.frame (encodeCompressionTable table) prior machine)).map
          (fun c => Reification.terminal c.control)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, support, rfl⟩
  simp only [NativeCode.frame] at seen
  rw [law, PMF.map_comp, PMF.map_comp, PMF.mem_support_map_iff] at seen
  obtain ⟨out, _, result⟩ := seen
  exact result.symm

/-- Redundant blanks do not change the actual first-halt time jointly
with packet, shared cache and complete transcript. -/
theorem typed_runtime_equivalent_first_joint {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (entry : machine.Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList)))) :
    (runToBoundary (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun c => Reification.terminal c.control) (runtimeHashSteps n κ message.length)
      (NativeCode.frame (encodeCompressionTable table) prior machine)).map
        (fun result => (CellEquivalence.packetObservation result.1, result.2)) =
    (runToBoundary (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun c => Reification.terminal c.control) (runtimeHashSteps n κ message.length)
      (NativeCode.frame (encodeCompressionTable table) prior
        (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))).map
          (fun result => (CellEquivalence.packetObservation result.1, result.2)) := by
  apply CellEquivalence.first_map
  · exact ⟨rfl, rfl, .running entry⟩
  · intro first second time he
    exact congrArg (fun observation => (observation, time)) (CellEquivalence.packet_eq first second he)

/-- Every supported native transfer exit satisfies the real hash-entry
cell condition after resumption. This only proves the interface; a linked
program must implement its own return and resumption control. -/
theorem runtime_transfer_hash_entry {κ : Nat} (message : List (Bits κ))
    (result : Machine.Configuration × Nat)
    (support : result ∈ (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
      (runtimeInputBits (message.map Bits.toList))).support) :
    (result.1.resumeAt 0).Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))) := by
  have h := Machine.NativeRequestTransfer.first_layout _ _ support
  simpa [Machine.Configuration.resumeAt, Machine.Configuration.initial] using h.resumeAt 0

/-- Ordinary native copying leaves a valid physical hashing entry. No
cell normalization, cache reset or transcript reset is used by this law. -/
theorem runtime_transfer_hash_packet {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (result : Machine.Configuration × Nat)
    (support : result ∈ (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
      (runtimeInputBits (message.map Bits.toList))).support) :
    (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (NativeCode.frame (encodeCompressionTable table) prior (result.1.resumeAt 0))).map CellEquivalence.packetObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) :=
  typed_runtime_equivalent_packet initial terminal message table prior _ (runtime_transfer_hash_entry message result support)

/-- Every actual branch makes one call per data block and one terminal
call, on top of the caller's existing trace. Cached calls are still counted. -/
theorem typed_runtime_equivalent_queries {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (entry : machine.Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList)
      (idealCompression n κ) (runtimeHashSteps n κ message.length)
      (NativeCode.frame (encodeCompressionTable table) prior machine)).support) :
    finish.reverseTrace.length = message.length + 1 + prior.length := by
  have seen : CellEquivalence.packetObservation finish ∈
      ((Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
        (runtimeHashSteps n κ message.length)
        (NativeCode.frame (encodeCompressionTable table) prior machine)).map CellEquivalence.packetObservation).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, support, rfl⟩
  rw [typed_runtime_equivalent_packet initial terminal message table prior machine entry,
    PMF.mem_support_map_iff] at seen
  obtain ⟨out, hout, he⟩ := seen
  have trace := congrArg (fun value : Option (List Bool) × IdealTable n κ × List (List Bool × List Bool) => value.2.2) he
  simp only [CellEquivalence.packetObservation] at trace
  rw [← trace, List.length_append, List.length_reverse, List.length_map]
  have count := iterate_trace_length RandomOracle.oracle initial (Foundation.Hash.encode terminal message) table out hout
  simpa using congrArg (fun length => length + prior.length) count

/-- Storage counts the actual physical entry, including all redundant
blanks, and every intermediate frame; equivalence never reduces its size. -/
theorem typed_runtime_actual_encoded_peak {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration) (elapsed : Nat)
    (within : elapsed ≤ runtimeHashSteps n κ message.length)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList)
      (idealCompression n κ) elapsed (NativeCode.frame (encodeCompressionTable table) prior machine)).support) :
    (EncodedStorage.codeEncoding.encode (runtimeHashCode initial.toList terminal.toList)).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound (runtimeHashCode initial.toList terminal.toList) machine.pc
      (ControllerExtent.frameExtent (tableSize n κ)
        (NativeCode.frame (encodeCompressionTable table) prior machine))
      (runtimeHashSteps n κ message.length) (entryIncrement n κ) n := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ) (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeHashSteps n κ message.length) elapsed within
    (NativeCode.frame (encodeCompressionTable table) prior machine) target support

end Foundation.Hash.Native
