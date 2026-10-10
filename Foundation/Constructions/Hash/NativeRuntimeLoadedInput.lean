import Foundation.Constructions.Hash.NativeRuntimeTypedExecution
import Foundation.Crypto.Semantics.Oracle.NativePacketLaunch

/-! Hashing the exact input layout produced by the existing raw bit loader.
The represented trailing blank is retained at every point. This certifies
execution from that physical layout and the preceding charged raw-loader
handoff. Request allocation and encoding are not free runtime operations. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric
open TimedExecution
set_option backward.isDefEq.respectTransparency false

def runtimeLoadedFrame {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n))
    (message : List (Bits κ)) : Configuration (IdealTable n κ) :=
  ⟨encodeCompressionTable table,
    .running {inputTape := ResponseLoading.loaded (runtimeInputBits (message.map Bits.toList))}, []⟩

def runtimeLoadedFinalInput (message : List (List Bool)) : Tape :=
  FixedWidthCopy.frontier ((runtimePayloadBits message).reverse.map some) [some true, none]

/-- The request length counts one marker per block and the terminal marker. -/
theorem typed_runtime_input_length {κ : Nat} (message : List (Bits κ)) :
    (runtimeInputBits (message.map Bits.toList)).length = message.length * (κ + 1) + 1 := by
  induction message with
  | nil => simp [runtimeInputBits, runtimePayloadBits]
  | cons payload rest ih =>
      have split : runtimeInputBits ((payload :: rest).map Bits.toList) =
          false :: (payload.toList ++ runtimeInputBits (rest.map Bits.toList)) := by
        simp [runtimeInputBits, runtimePayloadBits, List.append_assoc]
      rw [split, List.length_cons, List.length_append, ih]
      simp only [show payload.toList.length = κ by simp, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The real raw loader reaches exactly the initial frame used by the typed
hash proof; its private table and represented trailing blank are unchanged. -/
theorem typed_runtime_launch_first_joint {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) :
    runToBoundary
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      NativePacketLaunch.runningBoundary (3 * (message.length * (κ + 1) + 1) + 4)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    PMF.pure (.running (.computing (runtimeLoadedFrame table message)),
      3 * (message.length * (κ + 1) + 1) + 4) := by
  have h := NativePacketLaunch.launch_first_joint
    (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
    (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList))
  simpa only [typed_runtime_input_length, NativePacketLaunch.handoffFrame,
    Machine.NativePacketService.loaded, Machine.Configuration.swapTapes, runtimeLoadedFrame] using h

/-- Real execution continues from the loaded hash entry after charging the
exact preparation duration; no analysis padding is charged to the caller. -/
theorem typed_runtime_launch_continues {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (horizon : Nat)
    (enough : 3 * (message.length * (κ + 1) + 1) + 4 ≤ horizon) :
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      horizon (.preparing (encodeCompressionTable table)
        (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (horizon - (3 * (message.length * (κ + 1) + 1) + 4))
      (.running (.computing (runtimeLoadedFrame table message))) := by
  have h := NativePacketLaunch.launch_continues
    (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
    (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList)) horizon
    (by simpa only [typed_runtime_input_length] using enough)
  simpa only [typed_runtime_input_length, NativePacketLaunch.handoffFrame,
    Machine.NativePacketService.loaded, Machine.Configuration.swapTapes, runtimeLoadedFrame] using h

/-- Exact original typed hash law on the loader's actual finite-cell layout. -/
theorem typed_runtime_loaded_run {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length) (runtimeLoadedFrame table message) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeLoadedFinalInput (message.map Bits.toList))) := by
  simpa only [runtimeLoadedFrame, runtimeLoadedFinalInput, FixedWidthCopy.frontier,
    ResponseLoading.loaded, ResponseLoading.fromCells, List.append_nil] using
    typed_runtime_prefixFree_framed_run initial terminal message table [] [none]

/-- The loader's extra blank cannot cause fuel exhaustion on valid inputs. -/
theorem typed_runtime_loaded_halts {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.HaltsWithin (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeLoadedFrame table message) (runtimeHashSteps n κ message.length) := by
  intro finish support
  rw [typed_runtime_loaded_run, PMF.mem_support_map_iff] at support
  obtain ⟨out, _, rfl⟩ := support
  rfl

/-- Every compression call, including a cache hit, remains in the trace. -/
theorem typed_runtime_loaded_queries {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length) (runtimeLoadedFrame table message)).support) :
    finish.reverseTrace.length = message.length + 1 := by
  rw [typed_runtime_loaded_run, PMF.mem_support_map_iff] at support
  obtain ⟨out, hOut, rfl⟩ := support
  have h := iterate_trace_length RandomOracle.oracle initial (Foundation.Hash.encode terminal message) table out hOut
  simpa [typedHashFinish] using h

/-- All intermediate represented cells, including the loader's final blank,
private compression cache and complete trace, contribute to this bound. -/
theorem typed_runtime_loaded_encoded_peak {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (elapsed : Nat)
    (within : elapsed ≤ runtimeHashSteps n κ message.length)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      elapsed (runtimeLoadedFrame table message)).support) :
    (EncodedStorage.codeEncoding.encode (runtimeHashCode initial.toList terminal.toList)).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound (runtimeHashCode initial.toList terminal.toList) 0
      (ControllerExtent.frameExtent (tableSize n κ) (runtimeLoadedFrame table message))
      (runtimeHashSteps n κ message.length) (entryIncrement n κ) n := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ) (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeHashSteps n κ message.length) elapsed within (runtimeLoadedFrame table message) target support

end Foundation.Hash.Native
