import Foundation.Crypto.Semantics.Machine.NativeRepresentationRelation

/-! A native continuation observes only the cells described by its physical
entry, including correlations between both tapes. This factors a concrete
component's continuation through a logical result when a full-state cell
relation has been proved. It introduces no runtime projection or copy. -/
namespace Machine.NativeComponent
open Foundation.Probability
universe u v w x
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem continuation_observation (view : Input → Output → Value) (entry : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      ((P.procedure.execution.exit input output).resumeAt 0).Equivalent (entry (view input output)))
    (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (input : Input) :
    (P.procedure.execution.semantics input).bind (fun output =>
      (evalConfigWithin context ((P.procedure.execution.exit input output).resumeAt 0) horizon).map observe) =
    ((P.procedure.execution.semantics input).map (view input)).bind (fun value =>
      (evalConfigWithin context (entry value) horizon).map observe) := by
  rw [PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext output hOutput
  exact evalConfigWithin_map_eq_of_equivalent context _ _ (equivalent input output hOutput) horizon observe invariant

end Machine.NativeComponent
