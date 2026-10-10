import Foundation.Constructions.Hash.NativeRuntimeLinkedHash
import Foundation.Constructions.Hash.NativeRuntimeLaunchedExecution

/-! Raw-buffer loading, actual native copying and the relocated runtime hash
share one continuing controller. Direct handoff retains tape roles and the
prior trace. First-halt cost is genuine, not the padded analysis budget. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))

/-- Read and rewind the actual buffer, then hand over the unchanged tape
roles. Native copying is executed afterwards by the linked finite code. -/
theorem raw_linked_launch_first_joint :
    runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      NativePacketLaunch.runningBoundary (runtimePreparationSteps κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    PMF.pure (.running (.computing (runtimeTransferStart table message prior)), runtimePreparationSteps κ message.length) := by
  have h := NativePacketLaunch.launch_first_joint (runtimeLinkedHashCode initial.toList terminal.toList)
    (idealCompression n κ) (encodeCompressionTable table) (runtimeInputBits (message.map Bits.toList)) false prior
  simpa only [typed_runtime_input_length, runtimePreparationSteps, NativePacketLaunch.handoffFrame,
    runtimeTransferStart, NativeCode.frame,
    Machine.NativeRequestTransfer.initial] using h

/-- The native part of the same controller executes exactly the linked code
until its first halt; afterwards this controller can continue to export. -/
theorem raw_linked_stopped :
    runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedHashBoundary (runtimeLinkedHashSteps n κ message.length)
      (.running (.computing (runtimeTransferStart table message prior))) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).map (fun result =>
        (.running (.computing result.1), result.2)) := by
  exact runToBoundary_map
    (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
    (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
    (fun frame => Reification.terminal frame.control) launchedHashBoundary
    (fun frame => NativePacketLaunch.Control.running (.computing frame))
    (fun _ => rfl) (fun frame active => by
      simp [NativePacketLaunch.step, NativePacketComponent.step, active,
        PMF.map_comp, Function.comp_def]) _ _

/-- Exact raw-loading time plus the actual branch-dependent first native
halt time, jointly with all physical tapes, shared cache and complete trace. -/
theorem raw_linked_first_joint :
    runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedHashBoundary (runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).map (fun result =>
        (.running (.computing result.1), runtimePreparationSteps κ message.length + result.2)) := by
  have hp := raw_linked_launch_first_joint initial terminal message table prior
  have complete : ∀ result ∈ (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).support, Reification.terminal result.1.control = true := by
    apply runToBoundary_completes
    intro finish support
    rw [Reification.timed_eval_eq] at support
    exact runtime_linked_hash_halts initial terminal message table prior finish support
  rw [runToBoundary_compose _ NativePacketLaunch.runningBoundary launchedHashBoundary (fun _ => True)
    (by intros; trivial)
    (by intro control _ h; cases control <;> simp_all [NativePacketLaunch.runningBoundary, launchedHashBoundary])
    (runtimePreparationSteps κ message.length) (runtimeLinkedHashSteps n κ message.length)
    (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) trivial
    (by
      intro middle hm
      rw [hp, PMF.mem_support_pure_iff] at hm
      subst middle
      rfl)
    (by
      intro middle hm result hr
      rw [hp, PMF.mem_support_pure_iff] at hm
      subst middle
      rw [raw_linked_stopped, PMF.mem_support_map_iff] at hr
      obtain ⟨native, hn, rfl⟩ := hr
      exact complete native hn), hp, PMF.pure_bind, raw_linked_stopped, PMF.map_comp]
  rfl

/-- Removing padded halt transitions preserves the typed hash observation. -/
theorem linked_hash_stopped_observation :
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).map
        (fun result => CellEquivalence.packetObservation result.1) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  let P := Procedure.ofFixed
    (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
    (fun _ : Unit => runtimeTransferStart table message prior) (fun _ finish => finish)
    (fun _ => Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeLinkedHashSteps n κ message.length) (runtimeTransferStart table message prior))
    (fun _ => runtimeLinkedHashSteps n κ message.length)
    (fun _ => by
      rw [Reification.timed_eval_eq]
      change _ = PMF.map id _
      rw [PMF.map_id])
  have h := P.stopped_frames () (fun frame => Reification.terminal frame.control)
    (fun finish support => runtime_linked_hash_halts initial terminal message table prior finish support)
    (fun frame halted => by simp [Reification.timedStep, halted])
  change _ = PMF.map id (Reification.eval _ _ _ _) at h
  rw [PMF.map_id] at h
  simp only [P, TimedExecution.Procedure.ofFixed] at h
  rw [show (fun result : Configuration (IdealTable n κ) × Nat => CellEquivalence.packetObservation result.1) =
      CellEquivalence.packetObservation ∘ Prod.fst by rfl, ← PMF.map_comp, h]
  exact runtime_linked_hash_packet initial terminal message table prior

def rawHashObservation {State : Type*} : NativePacketLaunch.Control State →
    Option (Option (List Bool) × State × List (List Bool × List Bool))
  | .preparing _ _ => none
  | .running (.computing frame) => some (CellEquivalence.packetObservation frame)
  | .running (.exporting frame _) => some (CellEquivalence.packetObservation frame)

/-- Loading, copying, the actual return jump and hashing realize the typed
hash law. This observer is mathematical, not a free runtime packet reader. -/
theorem raw_linked_hash_packet :
    (runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedHashBoundary (runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).map
        (fun result => rawHashObservation result.1) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => some (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  rw [raw_linked_first_joint, PMF.map_comp]
  have h := congrArg (fun distribution => distribution.map some)
    (linked_hash_stopped_observation initial terminal message table prior)
  simpa only [PMF.map_comp, Function.comp_def, rawHashObservation] using h

/-- The same controller continues from the genuine halt using its actual
remaining budget; no intermediate boundary becomes an artificial stop. -/
theorem raw_linked_hash_continues (horizon : Nat)
    (enough : runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length ≤ horizon) :
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      horizon (.preparing (encodeCompressionTable table)
        (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).bind (fun result =>
        TimedExecution.eval
          (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
          (horizon - (runtimePreparationSteps κ message.length + result.2))
          (.running (.computing result.1))) := by
  rw [runToBoundary_law _ launchedHashBoundary
    (runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length)
    horizon _ enough, raw_linked_first_joint, PMF.bind_map]
  rfl

/-- Every first-halt result is a genuine completed native frame, and its
reported time includes raw loading and stays within the total budget. -/
theorem raw_linked_hash_halted (result : NativePacketLaunch.Control (IdealTable n κ) × Nat)
    (support : result ∈ (runToBoundary
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
      launchedHashBoundary (runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).support) :
    (∃ frame, result.1 = .running (.computing frame) ∧ Reification.terminal frame.control = true) ∧
    result.2 ≤ runtimePreparationSteps κ message.length + runtimeLinkedHashSteps n κ message.length := by
  rw [raw_linked_first_joint, PMF.mem_support_map_iff] at support
  obtain ⟨native, hn, rfl⟩ := support
  have complete : Reification.terminal native.1.control = true := by
    apply runToBoundary_completes _ _ _ _ _ native hn
    intro finish hf
    rw [Reification.timed_eval_eq] at hf
    exact runtime_linked_hash_halts initial terminal message table prior finish hf
  refine ⟨⟨native.1, rfl, complete⟩, ?_⟩
  have bounded := runToBoundary_bounded _ _ _ _ native hn
  exact Nat.add_le_add_left bounded _

/-- An upper bound in controller/native transitions, not wall-clock time.
The ideal compression capability's internal work remains external. -/
theorem runtimeRawHashSteps_formula (n κ count : Nat) :
    runtimePreparationSteps κ count + runtimeLinkedHashSteps n κ count =
      17 * (count * (κ + 1) + 1) + 17 +
        (3 * n + count * (7 * n + 8 * κ + 14) + (7 * n + 5 * κ + 13)) := by
  rw [runtimeLinkedHashSteps, runtimeHashSteps_formula]
  unfold runtimePreparationSteps runtimeTransferSteps
  omega

end Foundation.Hash.Native
