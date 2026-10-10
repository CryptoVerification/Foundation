import Foundation.Constructions.Hash.NativeRuntimeTypedExecution
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Foundation procedure certificates for the common runtime-input native hash.
The stopped certificate retains the joint first-arrival configuration/time
law, rather than treating a padded evaluator budget as the stopping time.
The returned configuration is a semantic observation, not a CPU decoder. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev RuntimeHashInput (n κ : Nat) := CompressionTable (Bits κ) (Bits n) × List (Bits κ)

noncomputable def runtimeFixedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    :
    Procedure (Reification.timedStep
      (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (RuntimeHashInput n κ) (Configuration (IdealTable n κ)) :=
  Procedure.ofFixed _
    (fun input => Configuration.initial (encodeCompressionTable input.1) (runtimeInputBits (input.2.map Bits.toList)))
    (fun _ finish => finish)
    (fun input => ((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
      (typedHashFinish (runtimeHaltPc (3 * n) n κ)
        (runtimeFinalInput (input.2.map Bits.toList))))
    (fun input => runtimeHashSteps n κ input.2.length)
    (fun input => by
      rw [Reification.timed_eval_eq]
      change Reification.eval _ _ _ _ = PMF.map id _
      rw [PMF.map_id]
      exact typed_runtime_prefixFree_run initial terminal input.2 input.1)

theorem runtimeFixedProcedure_exit {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ)
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ ((runtimeFixedProcedure initial terminal).semantics input).support) :
    Reification.terminal finish.control = true := by
  change finish ∈ (((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
    (typedHashFinish (runtimeHaltPc (3 * n) n κ)
      (runtimeFinalInput (input.2.map Bits.toList)))).support at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, _, rfl⟩ := support
  rfl

/-- Same actual transition system, stopped at its first native halt. The
existing boundary constructor removes absorbing padding from the cost law. -/
noncomputable def runtimeStoppedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    :
    Procedure (Reification.timedStep
      (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      (RuntimeHashInput n κ) (Configuration (IdealTable n κ)) :=
  (runtimeFixedProcedure initial terminal).liftBoundary
    (fun frame => Reification.terminal frame.control)
    (fun input finish support => runtimeFixedProcedure_exit initial terminal input finish support)
    (fun frame halted => by simp [Reification.timedStep, halted])
    (fun _ frame => frame) (fun _ _ => rfl)
    _ (fun frame => Reification.terminal frame.control) id (fun _ => rfl)
    (fun frame _ => by simp only [id_eq, PMF.map_id])

/-- Actual first-arrival cost and the whole physical exit configuration have
exactly the existing machine's stopped joint law. No observer is executed. -/
theorem runtimeStoppedProcedure_costed {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) :
    (runtimeStoppedProcedure initial terminal).costed input =
      runToBoundary
        (Reification.timedStep
          (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
        (fun frame => Reification.terminal frame.control) (runtimeHashSteps n κ input.2.length)
        (Configuration.initial (encodeCompressionTable input.1) (runtimeInputBits (input.2.map Bits.toList))) := by
  change PMF.map id _ = _
  exact PMF.map_id _

/-- Marginalizing genuine first-arrival time gives the original typed hash
experiment's final state, digest and trace in their native representations. -/
theorem runtimeStoppedProcedure_correct {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) :
    ((runtimeStoppedProcedure initial terminal).costed input).map Prod.fst =
      ((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
        (typedHashFinish (runtimeHaltPc (3 * n) n κ)
          (runtimeFinalInput (input.2.map Bits.toList))) :=
  (runtimeStoppedProcedure initial terminal).correct input

/-- The numeric formula bounds actual first-arrival time, not post-halt
padding, and holds jointly with every supported physical exit. -/
theorem runtimeStoppedProcedure_bounded {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((runtimeStoppedProcedure initial terminal).costed input).support) :
    result.2 ≤ runtimeHashSteps n κ input.2.length :=
  (runtimeStoppedProcedure initial terminal).bounded input result support

/-- Every stopped branch reaches a genuine native halt, not fuel exhaustion. -/
theorem runtimeStoppedProcedure_halted {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((runtimeStoppedProcedure initial terminal).costed input).support) :
    Reification.terminal result.1.control = true :=
  runtimeFixedProcedure_exit initial terminal input result.1
    ((runtimeStoppedProcedure initial terminal).result_support input result support)

/-- The stopped physical state is reachable at its reported actual time.
Apply the proved peak bound to that time, keeping state/time dependence. -/
theorem runtimeStoppedProcedure_encoded_peak {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((runtimeStoppedProcedure initial terminal).costed input).support) :
    (EncodedStorage.codeEncoding.encode
      (runtimeHashCode initial.toList terminal.toList)).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode result.1).length ≤
    EncodedStorage.bound
      (runtimeHashCode initial.toList terminal.toList) 0
      (ControllerExtent.frameExtent (tableSize n κ)
        (Configuration.initial (encodeCompressionTable input.1) (runtimeInputBits (input.2.map Bits.toList))))
      (runtimeHashSteps n κ input.2.length) (entryIncrement n κ) n := by
  have time := runtimeStoppedProcedure_bounded initial terminal input result support
  rw [runtimeStoppedProcedure_costed] at support
  have reachable := runToBoundary_reachable _ _ _ _ result support
  rw [Reification.timed_eval_eq] at reachable
  exact typed_runtime_prefixFree_encoded_peak initial terminal input.2 input.1 result.2 time result.1 reachable

end Foundation.Hash.Native
