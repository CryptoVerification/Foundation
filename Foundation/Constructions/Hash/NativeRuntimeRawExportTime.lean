import Foundation.Constructions.Hash.NativeRuntimeRawExport
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentTime

/-! Actual first physical return, jointly with the unchanged native frame,
for raw input loading, native request copying, hashing and packet export. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def launchedReadyBoundary {State : Type*} : NativePacketLaunch.Control State → Bool
  | .preparing _ _ => false
  | .running component => NativePacketComponent.readyBoundary component

/-- Physical export has a constant actual cost on each completed frame,
including frames with redundant represented blank cells. -/
theorem runtime_cell_export_first_joint {State : Type*} (code : Code) (oracle : BitOracle State)
    (n : Nat) (frame : Configuration State) (valid : RuntimeCellExportable n frame) :
    runToBoundary (NativePacketComponent.step code oracle) NativePacketComponent.readyBoundary (2 * n + 5)
      (.computing frame) =
    PMF.pure (.exporting frame (.returned (runtimeExportPacket frame)), 2 * n + 5) := by
  have h := NativePacketComponent.export_cells_first_joint code oracle frame.state
    (runtimeExportMachine frame) frame.reverseTrace (runtimeExportPacket frame) valid.2.1 valid.2.2.1
  have frame_eq : (⟨frame.state, .running (runtimeExportMachine frame), frame.reverseTrace⟩ : Configuration State) = frame := by
    exact congrArg (fun control : Interactive.Control => (⟨frame.state, control, frame.reverseTrace⟩ : Configuration State)) valid.1.symm
  rw [frame_eq, valid.2.2.2] at h
  exact h

/-- The outer controller executes the identical first export, with its
actual time and completed frame retained. -/
theorem launched_cell_export_first_joint {State : Type*} (code : Code) (oracle : BitOracle State)
    (prior : List (List Bool × List Bool)) (n : Nat) (frame : Configuration State)
    (valid : RuntimeCellExportable n frame) :
    runToBoundary (NativePacketLaunch.step code oracle false prior) launchedReadyBoundary (2 * n + 5)
      (.running (.computing frame)) =
    PMF.pure (.running (.exporting frame (.returned (runtimeExportPacket frame))), 2 * n + 5) := by
  rw [runToBoundary_map (NativePacketComponent.step code oracle)
    (NativePacketLaunch.step code oracle false prior) NativePacketComponent.readyBoundary
    launchedReadyBoundary NativePacketLaunch.Control.running (fun _ => rfl)
    (fun _ _ => rfl), runtime_cell_export_first_joint code oracle n frame valid, PMF.pure_map]

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))

/-- Exact first-return law. Raw loading contributes its actual 3r+4 cost,
then the genuine native first-halt time, then exactly 2n+5 export steps.
Unused analysis fuel is not charged. -/
theorem raw_linked_export_first_joint :
    runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedReadyBoundary (runtimeRawExportSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).map (fun result =>
        (.running (.exporting result.1 (.returned (runtimeExportPacket result.1))),
          runtimePreparationSteps κ message.length + result.2 + (2 * n + 5))) := by
  have branch (result : Configuration (IdealTable n κ) × Nat)
      (support : result ∈ (runToBoundary
        (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
        (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
        (runtimeTransferStart table message prior)).support) :=
    launched_cell_export_first_joint (runtimeLinkedHashCode initial.toList terminal.toList)
      (idealCompression n κ) prior n result.1
      (runtime_linked_first_cell_exportable initial terminal message table prior result support)
  rw [runtimeRawExportSteps, runToBoundary_compose _ launchedHashBoundary launchedReadyBoundary
    (fun _ => True) (by intros; trivial)
    (by
      intro control _ h
      cases control with
      | preparing => rfl
      | running component =>
          cases component with
          | computing => rfl
          | exporting => simp [launchedHashBoundary] at h)
    (runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length) (2 * n + 5)
    (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) trivial
    (by
      intro middle hm
      obtain ⟨⟨frame, he, halted⟩, _⟩ := raw_linked_hash_halted initial terminal message table prior middle hm
      rw [he]
      exact halted)
    (by
      intro middle hm result hr
      rw [raw_linked_first_joint, PMF.mem_support_map_iff] at hm
      obtain ⟨native, hn, rfl⟩ := hm
      rw [branch native hn, PMF.mem_support_pure_iff] at hr
      subst result
      rfl), raw_linked_first_joint, PMF.bind_map, PMF.map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result support
  dsimp only [Function.comp_def]
  rw [branch result support, PMF.pure_map]

/-- The actual first return preserves the typed tag/table/history law. -/
theorem raw_linked_export_first_packet :
    (runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedReadyBoundary (runtimeRawExportSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).map
        (fun result => rawReturnedObservation result.1) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => some (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  rw [raw_linked_export_first_joint, PMF.map_comp]
  have h := raw_linked_export_packet initial terminal message table prior
  rw [raw_linked_export_frames, PMF.map_comp] at h
  exact h

/-- The proved first-return law remains a boundary in the unchanged
controller. Any later execution uses exactly its actual residual budget. -/
theorem raw_linked_export_continues (horizon : Nat)
    (enough : runtimeRawExportSteps n κ message.length ≤ horizon) :
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      horizon (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).bind (fun result =>
        TimedExecution.eval
          (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
          (horizon - (runtimePreparationSteps κ message.length + result.2 + (2 * n + 5)))
          (.running (.exporting result.1 (.returned (runtimeExportPacket result.1))))) := by
  rw [runToBoundary_law _ launchedReadyBoundary (runtimeRawExportSteps n κ message.length) horizon _ enough,
    raw_linked_export_first_joint, PMF.bind_map]
  rfl

end Foundation.Hash.Native
