import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionSecrecy
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeBoundaryContinuation

/-! Actual first-halt costs for the raw-plaintext encryption code and their
connection to time-aware native observations. This retains the ciphertext /
actual-cost joint law; it does not claim that the cost is secret-independent. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def arrival : NativeComponent (List Bool) Configuration := link.component.firstArrival

theorem arrival_code : arrival.procedure.code = link.code := rfl

theorem arrival_budget (message : List Bool) : arrival.procedure.execution.budget message = 61 * message.length + 40 :=
  budget message

theorem arrival_semantics (message : List Bool) :
    arrival.procedure.execution.semantics message = link.native.execution.semantics message := by
  change (link.native.execution.semantics message).map (fun state => state) = _
  exact PMF.map_id _

theorem arrival_costed (message : List Bool) :
    arrival.procedure.execution.costed message =
      TimedExecution.runToBoundary (stepPMF link.code) Configuration.halted (61 * message.length + 40)
        (Configuration.initial message) := by
  change link.component.firstArrival.procedure.execution.costed message = _
  rw [link.component.firstArrival_costed]
  change TimedExecution.runToBoundary _ _ (link.native.execution.budget message)
    (link.native.execution.entry message) = _
  rw [budget, entry]
  rfl

theorem arrival_costed_horizon (message : List Bool) (horizon : Nat)
    (hTime : 61 * message.length + 40 ≤ horizon) :
    TimedExecution.runToBoundary (stepPMF link.code) Configuration.halted horizon (Configuration.initial message) =
      arrival.procedure.execution.costed message := by
  have h := link.component.firstArrival_costed_horizon message horizon (by
    change link.native.execution.budget message ≤ horizon
    rw [budget]
    exact hTime)
  change TimedExecution.runToBoundary _ _ _ (link.native.execution.entry message) = _ at h
  rwa [entry] at h

theorem arrival_operational : TimedExecution.Procedure.Operational arrival.procedure.execution :=
  link.component.firstArrival_operational

theorem arrival_scratch_blank (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (arrival.procedure.execution.costed message).support) :
    result.1.outputTape.Equivalent ({} : Tape) := by
  have h := arrival.procedure.execution.result_support message result hResult
  rw [arrival_semantics] at h
  exact scratch_blank message result.1 h

theorem arrival_ciphertext_uniform {width : Nat} (message : Bits width) :
    (arrival.procedure.execution.costed message.toList).map (fun result => result.1.inputTape.bits) =
      (uniform (Bits width)).map Bits.toList := by
  have h := congrArg (fun distribution => distribution.map (fun state => state.inputTape.bits))
    (arrival.procedure.execution.correct message.toList)
  rw [arrival_semantics, ciphertext_uniform] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

private theorem arrival_entry_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (arrival.procedure.execution.semantics message).support) :
    (target.resumeAt 0).Equivalent (continuationEntry target.inputTape.bits) := by
  rw [arrival_semantics] at hTarget
  exact continuation_entry_equivalent message target hTarget

theorem arrival_time_continuation {Observed : Type u} (message : List Bool)
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (arrival.procedure.execution.costed message).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) =
    ((arrival.procedure.execution.costed message).map (fun result => (result.1.inputTape.bits, result.2))).bind
      (fun result => (evalConfigWithin (context result.2) (continuationEntry result.1) (horizon result.2)).map (observe result.2)) := by
  exact arrival.continuation_time_observation (fun _ state => state.inputTape.bits) continuationEntry
    arrival_entry_equivalent context horizon observe invariant message

theorem arrival_time_secrecy_of_joint_eq {width : Nat} (left right : Bits width)
    (sameJoint : (arrival.procedure.execution.costed left.toList).map (fun result => (result.1.inputTape.bits, result.2)) =
      (arrival.procedure.execution.costed right.toList).map (fun result => (result.1.inputTape.bits, result.2)))
    {Observed : Type u} (context : Nat → Program) (horizon : Nat → Nat)
    (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (arrival.procedure.execution.costed left.toList).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) =
    (arrival.procedure.execution.costed right.toList).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) := by
  rw [arrival_time_continuation left.toList context horizon observe invariant,
    arrival_time_continuation right.toList context horizon observe invariant, sameJoint]

theorem arrival_boundary_continuation {Observed : Type u} (message : List Bool)
    (context : Nat → Program) (boundary : Nat → Configuration → Bool)
    (boundaryInvariant : ∀ time first second, first.Equivalent second → boundary time first = boundary time second)
    (fuel : Nat → Nat) (observe : Nat → Configuration × Nat → Observed)
    (invariant : ∀ time first second elapsed, first.Equivalent second →
      observe time (first, elapsed) = observe time (second, elapsed)) :
    (arrival.procedure.execution.costed message).bind (fun result =>
      (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        (result.1.resumeAt 0)).map (observe result.2)) =
    ((arrival.procedure.execution.costed message).map (fun result => (result.1.inputTape.bits, result.2))).bind
      (fun result => (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2)
        (fuel result.2) (continuationEntry result.1)).map (observe result.2)) := by
  exact arrival.continuation_boundary_observation (fun _ state => state.inputTape.bits) continuationEntry
    arrival_entry_equivalent context boundary boundaryInvariant fuel observe invariant message

end Machine.GeneratedBlockEncryption
