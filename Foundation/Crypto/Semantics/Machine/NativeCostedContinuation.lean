import Foundation.Crypto.Semantics.Machine.NativeContinuationObservation

/-! Factor a native continuation through a logical result while retaining
the original result/time correlation. The theorem does not assert that
the first stage's time is independent of secrets or of its output. -/
namespace Machine.NativeComponent
open Foundation.Probability
universe u v w x
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem continuation_costed_observation (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (input : Input) :
    (P.procedure.execution.costed input).bind (fun result =>
      (evalConfigWithin context ((P.procedure.execution.exit input result.1).resumeAt 0) horizon).map
        (fun state => (observe state, result.2))) =
    ((P.procedure.execution.costed input).map (fun result => (view input result.1, result.2))).bind
      (fun result => (evalConfigWithin context (entry result.1) horizon).map
        (fun state => (observe state, result.2))) := by
  rw [PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  exact evalConfigWithin_map_eq_of_equivalent context _ _
    (equivalent input result.1 (P.procedure.execution.result_support input result hResult)) horizon
    (fun state => (observe state, result.2)) (fun first second h => congrArg (fun value => (value, result.2)) (invariant first second h))

end Machine.NativeComponent
