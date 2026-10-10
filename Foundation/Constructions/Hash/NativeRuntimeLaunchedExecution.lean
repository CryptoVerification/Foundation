import Foundation.Constructions.Hash.NativeRuntimeLoadedInput
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Actual raw loading followed by the common native hash, stopped at the
first native halt. Loading and hashing share the same physical controller;
the joint law keeps the cache, all tapes, trace and genuine elapsed time. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def launchedHashBoundary {State : Type*} : NativePacketLaunch.Control State → Bool
  | .preparing _ _ => false
  | .running (.computing frame) => Reification.terminal frame.control
  | .running (.exporting _ _) => true

def runtimePreparationSteps (κ count : Nat) : Nat := 3 * (count * (κ + 1) + 1) + 4

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n))

/-- Before native halt, the launched controller executes precisely the
same hash transitions as the original interactive machine. -/
theorem launched_hash_stopped :
    runToBoundary
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      launchedHashBoundary (runtimeHashSteps n κ message.length)
      (.running (.computing (runtimeLoadedFrame table message))) =
    (runToBoundary
      (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ message.length)
      (runtimeLoadedFrame table message)).map (fun result =>
        (.running (.computing result.1), result.2)) := by
  exact runToBoundary_map
    (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
    (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
    (fun frame => Reification.terminal frame.control) launchedHashBoundary
    (fun frame => NativePacketLaunch.Control.running (.computing frame))
    (fun _ => rfl) (fun frame active => by
      simp [NativePacketLaunch.step, NativePacketComponent.step, active,
        PMF.map_comp, Function.comp_def]) _ _

/-- The entire raw-buffer-to-native-halt execution has the actual joint
first-arrival law, adding the exact loader time to each native branch. -/
theorem launched_hash_first_joint :
    runToBoundary
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      launchedHashBoundary
      (runtimePreparationSteps κ message.length + runtimeHashSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ message.length)
      (runtimeLoadedFrame table message)).map (fun result =>
        (.running (.computing result.1), runtimePreparationSteps κ message.length + result.2)) := by
  have hp := typed_runtime_launch_first_joint initial terminal message table
  change runToBoundary _ _ (runtimePreparationSteps κ message.length) _ =
    PMF.pure (NativePacketLaunch.Control.running (.computing (runtimeLoadedFrame table message)), runtimePreparationSteps κ message.length) at hp
  have complete : ∀ result ∈ (runToBoundary
      (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ message.length)
      (runtimeLoadedFrame table message)).support, Reification.terminal result.1.control = true := by
    apply runToBoundary_completes
    intro finish support
    rw [Reification.timed_eval_eq] at support
    exact typed_runtime_loaded_halts initial terminal message table finish support
  rw [runToBoundary_compose _ NativePacketLaunch.runningBoundary launchedHashBoundary (fun _ => True)
    (by intros; trivial)
    (by intro control _ h; cases control <;> simp_all [NativePacketLaunch.runningBoundary, launchedHashBoundary])
    (runtimePreparationSteps κ message.length) (runtimeHashSteps n κ message.length)
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
      rw [launched_hash_stopped, PMF.mem_support_map_iff] at hr
      obtain ⟨native, hn, rfl⟩ := hr
      exact complete native hn), hp, PMF.pure_bind, launched_hash_stopped, PMF.map_comp]
  rfl

/-- Native stopped frames have the original typed hash marginal. This uses
proved physical completion and absorbing native halt, not a free observer. -/
theorem loaded_hash_stopped_frames :
    (runToBoundary
      (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ message.length)
      (runtimeLoadedFrame table message)).map Prod.fst =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeLoadedFinalInput (message.map Bits.toList))) := by
  let P := Procedure.ofFixed
    (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
    (fun _ : Unit => runtimeLoadedFrame table message) (fun _ finish => finish)
    (fun _ => ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeLoadedFinalInput (message.map Bits.toList))))
    (fun _ => runtimeHashSteps n κ message.length)
    (fun _ => by
      rw [Reification.timed_eval_eq]
      change Reification.eval _ _ _ _ = PMF.map id _
      rw [PMF.map_id]
      exact typed_runtime_loaded_run initial terminal message table)
  have h := P.stopped_frames () (fun frame => Reification.terminal frame.control)
    (fun finish support => by
      change finish ∈ (((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
        (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeLoadedFinalInput (message.map Bits.toList)))).support at support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨out, _, rfl⟩ := support
      rfl)
    (fun frame halted => by simp [Reification.timedStep, halted])
  change _ = PMF.map id (((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
    (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeLoadedFinalInput (message.map Bits.toList)))) at h
  rw [PMF.map_id] at h
  exact h

/-- Marginalizing the actual raw-loading/native-halt execution recovers the
original typed hash experiment in its complete physical representation. -/
theorem launched_hash_frames :
    (runToBoundary
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      launchedHashBoundary
      (runtimePreparationSteps κ message.length + runtimeHashSteps n κ message.length)
      (.preparing (encodeCompressionTable table) (.loading (runtimeInputBits (message.map Bits.toList)) {}))).map Prod.fst =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => NativePacketLaunch.Control.running (.computing
        (typedHashFinish (runtimeHaltPc (3 * n) n κ)
          (runtimeLoadedFinalInput (message.map Bits.toList)) out))) := by
  rw [launched_hash_first_joint, PMF.map_comp]
  have h := congrArg (fun distribution => distribution.map
    (fun frame => NativePacketLaunch.Control.running (.computing frame)))
    (loaded_hash_stopped_frames initial terminal message table)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Export continues after the genuine native halt. The hash boundary is
intermediate in this controller, so residual execution cannot be discarded. -/
theorem launched_hash_continues (horizon : Nat)
    (enough : runtimePreparationSteps κ message.length + runtimeHashSteps n κ message.length ≤ horizon) :
    TimedExecution.eval
      (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      horizon (.preparing (encodeCompressionTable table)
        (.loading (runtimeInputBits (message.map Bits.toList)) {})) =
    (runToBoundary
      (Reification.timedStep (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ message.length)
      (runtimeLoadedFrame table message)).bind (fun result =>
        TimedExecution.eval
          (NativePacketLaunch.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
          (horizon - (runtimePreparationSteps κ message.length + result.2))
          (.running (.computing result.1))) := by
  rw [runToBoundary_law _ launchedHashBoundary
    (runtimePreparationSteps κ message.length + runtimeHashSteps n κ message.length)
    horizon _ enough, launched_hash_first_joint, PMF.bind_map]
  rfl

end Foundation.Hash.Native
