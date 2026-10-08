import Foundation.Crypto.Semantics.Machine.NativeCostedContinuation
import Foundation.Crypto.Semantics.Probability.ObserverBound
import Foundation.Crypto.Semantics.ProcedureCostObservation

/-! Time-aware continuations and quantitative security. The observer may
choose its native code and finite horizon from the reported first-stage
cost. The full view/cost joint law is retained. Actual arrival at that
reported cost requires the component's separate Operational certificate. -/
namespace Machine.NativeComponent
open Foundation.Probability
open scoped ENNReal
universe u v w x
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem continuation_time_observation (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second)
    (input : Input) :
    (P.procedure.execution.costed input).bind (fun result =>
      (evalConfigWithin (context result.2) ((P.procedure.execution.exit input result.1).resumeAt 0)
        (horizon result.2)).map (observe result.2)) =
    ((P.procedure.execution.costed input).map (fun result => (view input result.1, result.2))).bind
      (fun result => (evalConfigWithin (context result.2) (entry result.1) (horizon result.2)).map (observe result.2)) := by
  rw [PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  exact evalConfigWithin_map_eq_of_equivalent (context result.2) _ _
    (equivalent input result.1 (P.procedure.execution.result_support input result hResult))
    (horizon result.2) (observe result.2) (invariant result.2)

theorem continuation_time_eq_of_joint_eq
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input)
    (sameJoint : (P.procedure.execution.costed left).map (fun result => (view left result.1, result.2)) =
      (P.procedure.execution.costed right).map (fun result => (view right result.1, result.2)))
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (P.procedure.execution.costed left).bind (fun result =>
      (evalConfigWithin (context result.2) ((P.procedure.execution.exit left result.1).resumeAt 0)
        (horizon result.2)).map (observe result.2)) =
    (P.procedure.execution.costed right).bind (fun result =>
      (evalConfigWithin (context result.2) ((P.procedure.execution.exit right result.1).resumeAt 0)
        (horizon result.2)).map (observe result.2)) := by
  rw [P.continuation_time_observation view entry equivalent context horizon observe invariant left,
    P.continuation_time_observation view entry equivalent context horizon observe invariant right, sameJoint]

theorem continuation_time_bound
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input) (allowed : ((Value × Nat) → PMF Bool) → Prop) (epsilon : ℝ≥0∞)
    (bound : ObserverBound allowed
      ((P.procedure.execution.costed left).map (fun result => (view left result.1, result.2)))
      ((P.procedure.execution.costed right).map (fun result => (view right result.1, result.2))) epsilon)
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Bool)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second)
    (admitted : allowed (fun result =>
      (evalConfigWithin (context result.2) (entry result.1) (horizon result.2)).map (observe result.2))) :
    probabilityGap
      (eventProb ((P.procedure.execution.costed left).bind (fun result =>
        (evalConfigWithin (context result.2) ((P.procedure.execution.exit left result.1).resumeAt 0)
          (horizon result.2)).map (observe result.2))) (· = true))
      (eventProb ((P.procedure.execution.costed right).bind (fun result =>
        (evalConfigWithin (context result.2) ((P.procedure.execution.exit right result.1).resumeAt 0)
          (horizon result.2)).map (observe result.2))) (· = true)) ≤ epsilon := by
  rw [P.continuation_time_observation view entry equivalent context horizon observe invariant left,
    P.continuation_time_observation view entry equivalent context horizon observe invariant right]
  exact bound _ admitted

theorem continuation_time_eq_of_fixed_time
    (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (left right : Input) (duration : Nat)
    (fixedLeft : ∀ result, result ∈ (P.procedure.execution.costed left).support → result.2 = duration)
    (fixedRight : ∀ result, result ∈ (P.procedure.execution.costed right).support → result.2 = duration)
    (sameView : (P.procedure.execution.semantics left).map (view left) =
      (P.procedure.execution.semantics right).map (view right))
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (P.procedure.execution.costed left).bind (fun result =>
      (evalConfigWithin (context result.2) ((P.procedure.execution.exit left result.1).resumeAt 0)
        (horizon result.2)).map (observe result.2)) =
    (P.procedure.execution.costed right).bind (fun result =>
      (evalConfigWithin (context result.2) ((P.procedure.execution.exit right result.1).resumeAt 0)
        (horizon result.2)).map (observe result.2)) := by
  exact P.continuation_time_eq_of_joint_eq view entry equivalent left right
    (P.procedure.execution.costed_view_eq_of_fixed_time view left right duration fixedLeft fixedRight sameView)
    context horizon observe invariant

end Machine.NativeComponent
