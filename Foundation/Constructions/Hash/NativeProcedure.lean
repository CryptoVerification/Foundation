import Foundation.Constructions.Hash.NativeTypedExecution
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Foundation procedure certificates for the actual specialized native hash.
The stopped certificate retains the joint first-arrival configuration/time
law, rather than treating a padded evaluator budget as the stopping time.
The returned configuration is a semantic observation, not a CPU decoder. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev HashInput (n κ : Nat) := CompressionTable (Bits κ) (Bits n) × List Bool

def hashDuration (n : Nat) {κ : Nat} (message : List (Bits κ)) : Nat :=
  3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1

noncomputable def fixedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) :
    Procedure (Reification.timedStep
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) (idealCompression n κ))
      (HashInput n κ) (Configuration (IdealTable n κ)) :=
  Procedure.ofFixed _
    (fun input => Configuration.initial (encodeCompressionTable input.1) input.2)
    (fun _ finish => finish)
    (fun input => ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle input.1).map
      (typedHashFinish ((prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)).length - 1)
        (Tape.ofBits input.2)))
    (fun _ => hashDuration n message)
    (fun input => by
      rw [Reification.timed_eval_eq]
      change Reification.eval _ _ _ _ = PMF.map id _
      rw [PMF.map_id]
      exact typed_prefixFree_run initial terminal message input.2 input.1)

theorem fixedProcedure_exit {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ)
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ ((fixedProcedure initial terminal message).semantics input).support) :
    Reification.terminal finish.control = true := by
  change finish ∈ (((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle input.1).map
    (typedHashFinish ((prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)).length - 1)
      (Tape.ofBits input.2))).support at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, _, rfl⟩ := support
  rfl

/-- Same actual transition system, stopped at its first native halt. The
existing boundary constructor removes absorbing padding from the cost law. -/
noncomputable def stoppedProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) :
    Procedure (Reification.timedStep
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) (idealCompression n κ))
      (HashInput n κ) (Configuration (IdealTable n κ)) :=
  (fixedProcedure initial terminal message).liftBoundary
    (fun frame => Reification.terminal frame.control)
    (fun input finish support => fixedProcedure_exit initial terminal message input finish support)
    (fun frame halted => by simp [Reification.timedStep, halted])
    (fun _ frame => frame) (fun _ _ => rfl)
    _ (fun frame => Reification.terminal frame.control) id (fun _ => rfl)
    (fun frame _ => by simp only [id_eq, PMF.map_id])

/-- Actual first-arrival cost and the whole physical exit configuration have
exactly the existing machine's stopped joint law. No observer is executed. -/
theorem stoppedProcedure_costed {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ) :
    (stoppedProcedure initial terminal message).costed input =
      runToBoundary
        (Reification.timedStep
          (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) (idealCompression n κ))
        (fun frame => Reification.terminal frame.control) (hashDuration n message)
        (Configuration.initial (encodeCompressionTable input.1) input.2) := by
  change PMF.map id _ = _
  exact PMF.map_id _

/-- Marginalizing genuine first-arrival time gives the original typed hash
experiment's final state, digest and trace in their native representations. -/
theorem stoppedProcedure_correct {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ) :
    ((stoppedProcedure initial terminal message).costed input).map Prod.fst =
      ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle input.1).map
        (typedHashFinish ((prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)).length - 1)
          (Tape.ofBits input.2)) :=
  (stoppedProcedure initial terminal message).correct input

/-- The numeric formula bounds actual first-arrival time, not post-halt
padding, and holds jointly with every supported physical exit. -/
theorem stoppedProcedure_bounded {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((stoppedProcedure initial terminal message).costed input).support) :
    result.2 ≤ hashDuration n message :=
  (stoppedProcedure initial terminal message).bounded input result support

/-- Every stopped branch reaches a genuine native halt, not fuel exhaustion. -/
theorem stoppedProcedure_halted {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((stoppedProcedure initial terminal message).costed input).support) :
    Reification.terminal result.1.control = true :=
  fixedProcedure_exit initial terminal message input result.1
    ((stoppedProcedure initial terminal message).result_support input result support)

/-- The stopped physical state is reachable at its reported actual time.
Apply the proved peak bound to that time, keeping state/time dependence. -/
theorem stoppedProcedure_encoded_peak {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (message : List (Bits κ)) (input : HashInput n κ)
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ ((stoppedProcedure initial terminal message).costed input).support) :
    (EncodedStorage.codeEncoding.encode
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode result.1).length ≤
    EncodedStorage.bound
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) 0
      (ControllerExtent.frameExtent (tableSize n κ)
        (Configuration.initial (encodeCompressionTable input.1) input.2))
      (hashDuration n message) (entryIncrement n κ) n := by
  have time := stoppedProcedure_bounded initial terminal message input result support
  rw [stoppedProcedure_costed] at support
  have reachable := runToBoundary_reachable _ _ _ _ result support
  rw [Reification.timed_eval_eq] at reachable
  exact typed_prefixFree_encoded_peak initial terminal message input.2 input.1 result.2 time result.1 reachable

end Foundation.Hash.Native
