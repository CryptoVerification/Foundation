import Foundation.Constructions.Hash.NativeRuntimeRawExportTime
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! The raw native hash/export execution as an existing composable Procedure.
The costed contract reports the true first physical return; its output is the
complete physical control, rather than a normalized semantic representative. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem launched_ready_absorbing {State : Type*} (code : Code) (oracle : BitOracle State)
    (prior : List (List Bool × List Bool)) (control : NativePacketLaunch.Control State)
    (ready : launchedReadyBoundary control = true) :
    NativePacketLaunch.step code oracle false prior control = PMF.pure control := by
  cases control with
  | preparing => simp [launchedReadyBoundary] at ready
  | running component =>
      rw [NativePacketLaunch.step, NativePacketComponent.ready_absorbing code oracle component ready,
        PMF.pure_map]

theorem raw_linked_export_ready {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) (prior : List (List Bool × List Bool))
    (finish : NativePacketLaunch.Control (IdealTable n κ))
    (support : finish ∈ (TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      (runtimeRawExportSteps n κ input.2.length)
      (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {}))).support) :
    launchedReadyBoundary finish = true := by
  rw [raw_linked_export_frames, PMF.mem_support_map_iff] at support
  obtain ⟨result, _, rfl⟩ := support
  rfl

/-- The fixed horizon is used only to establish the full physical execution.
The next constructor removes absorbing padding from the reported cost. -/
noncomputable def runtimeRawFixedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) :=
  Procedure.ofFixed
    (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
    (fun input : RuntimeHashInput n κ => NativePacketLaunch.Control.preparing (encodeCompressionTable input.1)
      (.loading (runtimeInputBits (input.2.map Bits.toList)) {}))
    (fun _ finish => finish)
    (fun input => TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      (runtimeRawExportSteps n κ input.2.length)
      (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {})))
    (fun input => runtimeRawExportSteps n κ input.2.length)
    (fun _ => (PMF.map_id _).symm)

/-- A first-return contract obtained from the concrete execution, without
an externally supplied implementation witness or a fixed-cost assumption. -/
noncomputable def runtimeRawStoppedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) :=
  (runtimeRawFixedProcedure initial terminal prior).liftBoundary launchedReadyBoundary
    (fun input finish support => raw_linked_export_ready initial terminal input prior finish support)
    (launched_ready_absorbing _ _ prior) (fun _ finish => finish) (fun _ _ => rfl)
    (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
    launchedReadyBoundary id (fun _ => rfl) (fun _ _ => (PMF.map_id _).symm)

theorem runtimeRawStoppedProcedure_budget {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    (runtimeRawStoppedProcedure initial terminal prior).budget input = runtimeRawExportSteps n κ input.2.length := rfl

/-- Actual first-return cost and every retained physical field are preserved
by the standard Foundation execution contract. -/
theorem runtimeRawStoppedProcedure_costed {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    (runtimeRawStoppedProcedure initial terminal prior).costed input =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ input.2.length)
      (runtimeTransferStart input.1 input.2 prior)).map (fun result =>
        (.running (.exporting result.1 (.returned (runtimeExportPacket result.1))),
          runtimePreparationSteps κ input.2.length + result.2 + (2 * n + 5))) := by
  change (runToBoundary _ _ _ _).map id = _
  rw [PMF.map_id]
  exact raw_linked_export_first_joint initial terminal input.2 input.1 prior

theorem runtimeRawStoppedProcedure_operational {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) :
    Procedure.Operational (runtimeRawStoppedProcedure initial terminal prior) := by
  apply Procedure.operational_liftBoundary

theorem runtimeRawStoppedProcedure_packet {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (input : RuntimeHashInput n κ) :
    ((runtimeRawStoppedProcedure initial terminal prior).semantics input).map rawReturnedObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
      (fun out => some (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  exact raw_linked_export_packet initial terminal input.2 input.1 prior

end Foundation.Hash.Native
