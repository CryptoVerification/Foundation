import Foundation.Crypto.Semantics.Machine.NativeContinuationObservation
import Foundation.Crypto.Semantics.Probability.ObserverBound

/-! Scheme-independent transport of equality of logical view distributions
through arbitrary finite native continuations. Full exit-cell relations are
required; timing and representation metadata are not silently hidden. -/
namespace Machine.NativeComponent
open Foundation.Probability
open scoped ENNReal
universe u v w x
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem continuation_eq_of_view_eq
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input)
    (sameView : (P.procedure.execution.semantics left).map (view left) =
      (P.procedure.execution.semantics right).map (view right))
    (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (P.procedure.execution.semantics left).bind (fun output =>
      (evalConfigWithin context ((P.procedure.execution.exit left output).resumeAt 0) horizon).map observe) =
    (P.procedure.execution.semantics right).bind (fun output =>
      (evalConfigWithin context ((P.procedure.execution.exit right output).resumeAt 0) horizon).map observe) := by
  rw [P.continuation_observation view entry equivalent context horizon observe invariant left,
    P.continuation_observation view entry equivalent context horizon observe invariant right, sameView]

theorem continuation_bound
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input) (allowed : (Value → PMF Bool) → Prop) (epsilon : ℝ≥0∞)
    (bound : ObserverBound allowed ((P.procedure.execution.semantics left).map (view left))
      ((P.procedure.execution.semantics right).map (view right)) epsilon)
    (context : Program) (horizon : Nat) (observe : Configuration → Bool)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (admitted : allowed (fun value => (evalConfigWithin context (entry value) horizon).map observe)) :
    probabilityGap
      (eventProb ((P.procedure.execution.semantics left).bind (fun output =>
        (evalConfigWithin context ((P.procedure.execution.exit left output).resumeAt 0) horizon).map observe)) (· = true))
      (eventProb ((P.procedure.execution.semantics right).bind (fun output =>
        (evalConfigWithin context ((P.procedure.execution.exit right output).resumeAt 0) horizon).map observe)) (· = true)) ≤ epsilon := by
  rw [P.continuation_observation view entry equivalent context horizon observe invariant left,
    P.continuation_observation view entry equivalent context horizon observe invariant right]
  exact bound _ admitted

end Machine.NativeComponent
