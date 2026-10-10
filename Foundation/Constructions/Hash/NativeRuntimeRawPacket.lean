import Foundation.Constructions.Hash.NativeRuntimeRawProcedure
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime

/-! The concrete raw-buffer hash as the existing physical-packet Handler.
The proof-side output view retains the complete actual native frame; the
packet has already been assembled by the executed exporter. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def runtimeRawReady {State : Type*} : NativePacketLaunch.Control State →
    Option (Configuration State × List Bool)
  | .preparing _ _ => none
  | .running component => NativePacketComponent.ready component

def runtimeRawRead {State : Type*} : NativePacketLaunch.Control State → Configuration State × List Bool
  | .preparing state _ => (⟨state, .finished false, []⟩, [])
  | .running component => NativePacketComponent.read component

def runtimeRawExit {State : Type*} (output : Configuration State × List Bool) : NativePacketLaunch.Control State :=
  .running (.exporting output.1 (.returned output.2))

noncomputable def runtimeRawPacketProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) :=
  (runtimeRawStoppedProcedure initial terminal prior).observe runtimeRawRead
    (fun _ => runtimeRawExit)
    (by
      intro input output support
      change output ∈ (TimedExecution.eval _ _ _).support at support
      rw [raw_linked_export_frames, PMF.mem_support_map_iff] at support
      obtain ⟨result, _, rfl⟩ := support
      rfl)

theorem runtimeRawPacketProcedure_response_length {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ)
    (output : Configuration (IdealTable n κ) × List Bool)
    (support : output ∈ ((runtimeRawPacketProcedure initial terminal prior).semantics input).support) :
    output.2.length = n := by
  change output ∈ ((TimedExecution.eval _ _ _).map runtimeRawRead).support at support
  rw [raw_linked_export_frames, PMF.map_comp, PMF.mem_support_map_iff] at support
  obtain ⟨result, hr, rfl⟩ := support
  exact (runtime_linked_first_cell_exportable initial terminal input.2 input.1 prior result hr).2.2.2

theorem runtimeRawPacketProcedure_costed {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    (runtimeRawPacketProcedure initial terminal prior).costed input =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ input.2.length)
      (runtimeTransferStart input.1 input.2 prior)).map (fun result =>
        ((result.1, runtimeExportPacket result.1),
          runtimePreparationSteps κ input.2.length + result.2 + (2 * n + 5))) := by
  change ((runtimeRawStoppedProcedure initial terminal prior).costed input).map _ = _
  rw [runtimeRawStoppedProcedure_costed, PMF.map_comp]
  rfl

theorem runtimeRawReady_absorbing {State : Type*} (code : Code) (oracle : BitOracle State)
    (prior : List (List Bool × List Bool)) (control : NativePacketLaunch.Control State)
    (ready : (runtimeRawReady control).isSome = true) :
    NativePacketLaunch.step code oracle false prior control = PMF.pure control := by
  apply launched_ready_absorbing code oracle prior control
  cases control <;> exact ready

theorem runtimeRawPacketProcedure_semantics {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    (runtimeRawPacketProcedure initial terminal prior).semantics input =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ input.2.length)
      (runtimeTransferStart input.1 input.2 prior)).map (fun result => (result.1, runtimeExportPacket result.1)) := by
  rw [← (runtimeRawPacketProcedure initial terminal prior).correct input,
    runtimeRawPacketProcedure_costed, PMF.map_comp]
  rfl

noncomputable def runtimeRawPacketHandler {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    PacketResponseService.Handler
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      runtimeRawReady where
  execution := (runtimeRawPacketProcedure initial terminal prior).reindex (fun _ : Unit => input)
  ready_exit _ := rfl
  read := runtimeRawRead
  read_exit _ := rfl
  responseCap := n
  response_bound := fun output support =>
    (runtimeRawPacketProcedure_response_length initial terminal prior input output support).le

/-- The existing service's first-ready condition is discharged from the
concrete first physical return, not assumed as an implementation witness. -/
theorem runtimeRawPacketHandler_exact {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    (runtimeRawPacketHandler initial terminal prior input).ExactFirstReady := by
  change (runToBoundary _ (fun control => (runtimeRawReady control).isSome)
    (runtimeRawExportSteps n κ input.2.length)
    (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {}))).map
      (fun result => (runtimeRawRead result.1, result.2)) =
    (runtimeRawPacketProcedure initial terminal prior).costed input
  have boundary : (fun control : NativePacketLaunch.Control (IdealTable n κ) => (runtimeRawReady control).isSome) =
      launchedReadyBoundary := by
    funext control
    cases control <;> rfl
  rw [boundary, raw_linked_export_first_joint, runtimeRawPacketProcedure_costed, PMF.map_comp]
  rfl

end Foundation.Hash.Native
