import Foundation.Constructions.Hash.NativeRuntimeRawExecution
import Foundation.Constructions.Hash.NativeRuntimeCellExport

/-! Execute raw loading, native copying, hashing and physical packet export
in one continuing controller. The endpoint retains the actual native frame,
compression cache and prior history. Compression remains an atomic capability. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def runtimeRawExportSteps (n κ count : Nat) : Nat :=
  runtimePreparationSteps κ count + runtimeLinkedHashSteps n κ count + (2 * n + 5)

/-- The response is read by the physical exporter, not by this proof-side
observation. Only an already returned packet is observable here. -/
def rawReturnedObservation {State : Type*} : NativePacketLaunch.Control State →
    Option (Option (List Bool) × State × List (List Bool × List Bool))
  | .running (.exporting frame (.returned packet)) => some (some packet, frame.state, frame.reverseTrace)
  | _ => none

theorem runtime_cell_export_run_later {State : Type*} (code : Code) (oracle : BitOracle State)
    (n : Nat) (frame : Configuration State) (valid : RuntimeCellExportable n frame)
    (fuel : Nat) (enough : 2 * n + 5 ≤ fuel) :
    TimedExecution.eval (NativePacketComponent.step code oracle) fuel (.computing frame) =
      PMF.pure (.exporting frame (.returned (runtimeExportPacket frame))) := by
  rw [show fuel = (2 * n + 5) + (fuel - (2 * n + 5)) by omega, eval_add,
    runtime_cell_export_run code oracle n frame valid, PMF.pure_bind]
  apply Block.eval_of_absorbing
  exact NativePacketComponent.ready_absorbing code oracle _ rfl

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))

/-- All physical stages execute on the same controller. The source is the
actual raw buffer; the endpoint contains the physically assembled packet. -/
theorem raw_linked_export_frames :
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      (runtimeRawExportSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).map (fun result =>
        .running (.exporting result.1 (.returned (runtimeExportPacket result.1)))) := by
  rw [raw_linked_hash_continues initial terminal message table prior
    (runtimeRawExportSteps n κ message.length) (by unfold runtimeRawExportSteps; omega)]
  rw [← PMF.bindOnSupport_eq_bind, PMF.map]
  rw [← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result support
  have bounded := runToBoundary_bounded _ _ _ _ result support
  have valid := runtime_linked_first_cell_exportable initial terminal message table prior result support
  rw [NativePacketLaunch.running_eval,
    runtime_cell_export_run_later _ _ n result.1 valid _ (by unfold runtimeRawExportSteps; omega), PMF.pure_map]
  rfl

/-- The physically returned tag, private table and complete shared history
have exactly the original typed-hash distribution. -/
theorem raw_linked_export_packet :
    (TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      (runtimeRawExportSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).map
        rawReturnedObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => some (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  rw [raw_linked_export_frames, PMF.map_comp]
  have observed := congrArg (fun distribution => distribution.map some)
    (linked_hash_stopped_observation initial terminal message table prior)
  simp only [PMF.map_comp, Function.comp_def] at observed
  rw [← observed]
  rw [PMF.map, PMF.map,
    ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result support
  have valid := runtime_linked_first_cell_exportable initial terminal message table prior result support
  have packet : CellEquivalence.packetObservation result.1 =
      (some (runtimeExportPacket result.1), result.1.state, result.1.reverseTrace) := by
    simp only [CellEquivalence.packetObservation]
    rw [valid.1]
    simp [Reification.packet, valid.2.1, runtimeExportPacket]
  simp only [Function.comp_def, rawReturnedObservation, packet]

end Foundation.Hash.Native
