import Foundation.Crypto.Semantics.Machine.NativeTimedObservationSecurity
import Foundation.Crypto.Semantics.Machine.NativeBoundaryObservation

/-! Continuations that expose both the first contract's cost and the actual
native boundary-arrival cost of the second stage. Exhausted-fuel results
remain results; successful termination needs a separate completion proof.
The caller may observe whether the returned state reached its boundary. -/
namespace Machine.NativeComponent
open Foundation.Probability
open scoped ENNReal
universe u v w x
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem continuation_boundary_observation
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (context : Nat → Program) (boundary : Nat → Configuration → Bool)
    (boundaryInvariant : ∀ time first second, first.Equivalent second → boundary time first = boundary time second)
    (fuel : Nat → Nat) (observe : Nat → Configuration × Nat → Observed)
    (invariant : ∀ time first second elapsed, first.Equivalent second →
      observe time (first, elapsed) = observe time (second, elapsed))
    (input : Input) :
    (P.procedure.execution.costed input).bind (fun result =>
      (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        ((P.procedure.execution.exit input result.1).resumeAt 0)).map (observe result.2)) =
    ((P.procedure.execution.costed input).map (fun result => (view input result.1, result.2))).bind
      (fun result => (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2)
        (fuel result.2) (entry result.1)).map (observe result.2)) := by
  rw [PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  exact runToBoundary_map_eq_of_equivalent (context result.2) (boundary result.2) (boundaryInvariant result.2)
    (fuel result.2) _ _
    (equivalent input result.1 (P.procedure.execution.result_support input result hResult))
    (observe result.2) (invariant result.2)

theorem continuation_boundary_bound
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input) (allowed : ((Value × Nat) → PMF Bool) → Prop) (epsilon : ℝ≥0∞)
    (bound : ObserverBound allowed
      ((P.procedure.execution.costed left).map (fun result => (view left result.1, result.2)))
      ((P.procedure.execution.costed right).map (fun result => (view right result.1, result.2))) epsilon)
    (context : Nat → Program) (boundary : Nat → Configuration → Bool)
    (boundaryInvariant : ∀ time first second, first.Equivalent second → boundary time first = boundary time second)
    (fuel : Nat → Nat) (observe : Nat → Configuration × Nat → Bool)
    (invariant : ∀ time first second elapsed, first.Equivalent second →
      observe time (first, elapsed) = observe time (second, elapsed))
    (admitted : allowed (fun result =>
      (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2)
        (fuel result.2) (entry result.1)).map (observe result.2))) :
    probabilityGap
      (eventProb ((P.procedure.execution.costed left).bind (fun result =>
        (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
          ((P.procedure.execution.exit left result.1).resumeAt 0)).map (observe result.2))) (· = true))
      (eventProb ((P.procedure.execution.costed right).bind (fun result =>
        (TimedExecution.runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
          ((P.procedure.execution.exit right result.1).resumeAt 0)).map (observe result.2))) (· = true)) ≤ epsilon := by
  rw [P.continuation_boundary_observation view entry equivalent context boundary boundaryInvariant fuel observe invariant left,
    P.continuation_boundary_observation view entry equivalent context boundary boundaryInvariant fuel observe invariant right]
  exact bound _ admitted

end Machine.NativeComponent
