import Foundation.Constructions.Hash.NativeRuntimeRawProcedure
import Foundation.Crypto.Semantics.Oracle.NativePacketLaunchResources

/-! One complete encoded peak bound for raw loading, native transfer/hash
and physical export, including fixed code/environment, every represented
blank, the full compression table, prior trace and retained export frame. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))

/-- The raw buffer and blank loading tape are physical entry conditions.
The fixed prior trace is included even before its handoff to the hash frame. -/
theorem runtimeRaw_initial_size :
    NativePacketLaunch.Resources.size (tableSize n κ) prior
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    max (tableSize n κ (encodeCompressionTable table))
      (max (ControllerExtent.traceExtent prior) (message.length * (κ + 1) + 1)) := by
  simp only [NativePacketLaunch.Resources.size, NativePacketService.Resources.size,
    NativePacketService.Resources.pc, NativePacketService.Resources.extent, Tape.cells,
    List.length_nil, typed_runtime_input_length]
  omega

/-- Full controller/environment encoding at every supported intermediate
time. Ideal compression is atomic in time, but its complete table is counted
in this storage bound. No smaller cell-equivalent state is substituted. -/
theorem raw_linked_export_encoded_peak (elapsed : Nat)
    (within : elapsed ≤ runtimeRawExportSteps n κ message.length)
    (target : NativePacketLaunch.Control (IdealTable n κ))
    (support : target ∈ (TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      elapsed (.preparing (encodeCompressionTable table)
        (.loading (runtimeInputBits (message.map Bits.toList)) {}))).support) :
    ((NativePacketLaunch.Resources.completeEncoding (tableEncoding n κ)).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, false, prior, target)).length ≤
    NativePacketLaunch.Resources.bitBound (runtimeLinkedHashCode initial.toList terminal.toList) prior
      (max (tableSize n κ (encodeCompressionTable table))
        (max (ControllerExtent.traceExtent prior) (message.length * (κ + 1) + 1)))
      (runtimeRawExportSteps n κ message.length) (entryIncrement n κ) n := by
  have h := NativePacketLaunch.Resources.peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior
    (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeRawExportSteps n κ message.length) elapsed within
    (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))
    target support
  rw [runtimeRaw_initial_size] at h
  exact h

/-- The actual first-return state satisfies the same complete peak bound;
reachability at the reported time is reused from the boundary semantics. -/
theorem raw_linked_export_first_encoded_peak
    (result : NativePacketLaunch.Control (IdealTable n κ) × Nat)
    (support : result ∈ (runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedReadyBoundary (runtimeRawExportSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).support) :
    ((NativePacketLaunch.Resources.completeEncoding (tableEncoding n κ)).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, false, prior, result.1)).length ≤
    NativePacketLaunch.Resources.bitBound (runtimeLinkedHashCode initial.toList terminal.toList) prior
      (max (tableSize n κ (encodeCompressionTable table))
        (max (ControllerExtent.traceExtent prior) (message.length * (κ + 1) + 1)))
      (runtimeRawExportSteps n κ message.length) (entryIncrement n κ) n := by
  exact raw_linked_export_encoded_peak initial terminal message table prior result.2
    (runToBoundary_bounded _ _ _ _ result support) result.1
    (runToBoundary_reachable _ _ _ _ result support)

/-- Every supported costed result of the existing execution certificate is
bounded at its actual reached physical state, not only at a padded horizon. -/
theorem runtimeRawStoppedProcedure_encoded_peak
    (input : RuntimeHashInput n κ) (result : NativePacketLaunch.Control (IdealTable n κ) × Nat)
    (support : result ∈ ((runtimeRawStoppedProcedure initial terminal prior).costed input).support) :
    ((NativePacketLaunch.Resources.completeEncoding (tableEncoding n κ)).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, false, prior, result.1)).length ≤
    NativePacketLaunch.Resources.bitBound (runtimeLinkedHashCode initial.toList terminal.toList) prior
      (max (tableSize n κ (encodeCompressionTable input.1))
        (max (ControllerExtent.traceExtent prior) (input.2.length * (κ + 1) + 1)))
      (runtimeRawExportSteps n κ input.2.length) (entryIncrement n κ) n := by
  exact raw_linked_export_encoded_peak initial terminal input.2 input.1 prior result.2
    ((runtimeRawStoppedProcedure initial terminal prior).bounded input result support) result.1
    (runtimeRawStoppedProcedure_operational initial terminal prior input result support)

end Foundation.Hash.Native
