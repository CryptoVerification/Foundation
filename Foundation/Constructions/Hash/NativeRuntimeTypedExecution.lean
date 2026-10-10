import Foundation.Constructions.Hash.NativeRuntimeHash
import Foundation.Constructions.Hash.NativeTypedExecution

/-! Runtime-message finite native hashing realizes the original typed ideal
compression experiment, including its shared private table and whole trace. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The same finite code works for every typed message; only the input tape
and execution budget depend on that message. -/
theorem typed_runtime_prefixFree_framed_run {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput tail : List (Option Bool)) :
    Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (⟨encodeCompressionTable table, .running { inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits (message.map Bits.toList)).map some ++ tail) }, []⟩ : Configuration (IdealTable n κ)) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ) (FixedWidthCopy.frontier ((runtimePayloadBits (message.map Bits.toList)).reverse.map some ++ beforeInput) (some true :: tail))) := by
  have raw := runtime_prefixFree_framed_run (idealCompression n κ) initial.toList terminal.toList
    (message.map Bits.toList) (encodeCompressionTable table)
    (fun state request answer ha => by simpa using (idealCompression_growth n κ state request answer ha).2)
    (by intro block hb; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb; simp) beforeInput tail
  simp only [show initial.toList.length = n by simp, show terminal.toList.length = κ by simp, List.length_map] at raw
  rw [raw]
  have blocks : Foundation.Hash.encode terminal.toList (message.map Bits.toList) =
      (Foundation.Hash.encode terminal message).map (fun block => (block.1, block.2.toList)) := by
    simp [Foundation.Hash.encode, List.map_map, Function.comp_def]
  change ((Foundation.Hash.iterate initial.toList _).run _ (encodeCompressionTable table)).map _ = _
  rw [blocks]
  have h := iterate_encoded_state_run Bits.toList
    (fun block : Bool × Bits κ => (block.1, block.2.toList)) encodeCompressionTable
    RandomOracle.oracle
    (Program.adaptOracle (fun pair : List Bool × (Bool × List Bool) => pair.1 ++ pair.2.1 :: pair.2.2)
      id (idealCompression n κ))
    (fun state previous payload => by
      change (idealCompression n κ (encodeCompressionTable state)
        (compressionPacket (previous, payload))).map id =
        (RandomOracle.oracle state (previous, payload)).map
          (fun answer => (encodeCompressionTable answer.1, answer.2.toList))
      rw [PMF.map_id]
      exact typed_compression_step state (previous, payload))
    initial (Foundation.Hash.encode terminal message) table
  rw [h]
  simp only [PMF.map_comp, Function.comp_def, Foundation.Hash.prefixFreeMD]
  congr 1
  funext out
  simp [hashFinish, typedHashFinish, encodeIterationOutcome, compressionPacket,
    List.map_map, Function.comp_def]

-- Retain the original unframed interface.
theorem typed_runtime_prefixFree_run {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList))) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeFinalInput (message.map Bits.toList))) := by
  simpa only [List.append_nil, runtimeInput_tape, runtimeFinalInput,
    Interactive.Configuration.initial, Machine.Configuration.initial] using
    typed_runtime_prefixFree_framed_run initial terminal message table [] []

/-- Native output equality is the same typed hash event. This is a semantic
observation, not an execution-time certificate for a separate verifier. -/
theorem typed_runtime_prefixFree_output {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (expected : Bits n) :
    eventProb (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList))))
      (fun finish => Reification.packet finish.control = some expected.toList) =
    eventProb ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table)
      (fun out => out.result = expected) := by
  rw [typed_runtime_prefixFree_run, eventProb_map]
  simp only [typedHashFinish_packet, Option.some.injEq, Bits.toList, List.ofFn_injective.eq_iff]

/-- Valid typed inputs always reach a native halt. -/
theorem typed_runtime_prefixFree_halts {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.HaltsWithin (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList)))
      (runtimeHashSteps n κ message.length) := by
  intro finish hFinish
  rw [typed_runtime_prefixFree_run, PMF.mem_support_map_iff] at hFinish
  obtain ⟨out, _, rfl⟩ := hFinish
  rfl

/-- Actual native capability calls count every data block and the terminal,
including requests already cached in the shared ideal compression table. -/
theorem typed_runtime_prefixFree_queries {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length)
      (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList)))).support) :
    finish.reverseTrace.length = message.length + 1 := by
  rw [typed_runtime_prefixFree_run, PMF.mem_support_map_iff] at support
  obtain ⟨out, hOut, rfl⟩ := support
  have h := iterate_trace_length RandomOracle.oracle initial (Foundation.Hash.encode terminal message) table out hOut
  simpa [typedHashFinish] using h

/-- The code, control, all tapes, transfer buffers, whole transcript and private
ideal table are bounded at every intermediate execution time. -/
theorem typed_runtime_prefixFree_encoded_peak {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (elapsed : Nat)
    (within : elapsed ≤ runtimeHashSteps n κ message.length)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      elapsed (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList)))).support) :
    (EncodedStorage.codeEncoding.encode (runtimeHashCode initial.toList terminal.toList)).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound (runtimeHashCode initial.toList terminal.toList) 0
      (ControllerExtent.frameExtent (tableSize n κ)
        (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList))))
      (runtimeHashSteps n κ message.length) (entryIncrement n κ) n := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ) (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeHashSteps n κ message.length) elapsed within
    (Configuration.initial (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList))) target support

end Foundation.Hash.Native
