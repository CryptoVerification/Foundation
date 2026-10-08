import Foundation.Crypto.Semantics.Oracle.OneUseSteps
import Foundation.Examples.OneUseSource

/-! Repeated contracts execute two actual rejected calls and genuine halt.
The second request is read from the first response tape, so it is not supplied
as an independent preselected request by the repetition contract. -/
namespace Foundation.OneUseIterationExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key sourceInput : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (tail : List (Option Bool))

def start : OneUseSource.Control State :=
  .source true key ⟨state, .running (OneUseSourceExamples.caller sourceInput request tail), trace⟩

noncomputable def execution :=
  OneUseSource.execution native OneUseSourceExamples.code oracle (2 * request.length + 47)

theorem budget : (execution native oracle request).budget (start key sourceInput state trace request tail) =
    2 * request.length + 47 :=
  Procedure.steps_budget _ _ _

theorem semantics : (execution native oracle request).semantics (start key sourceInput state trace request tail) =
    PMF.pure (OneUseSourceExamples.final key sourceInput state trace request tail) := by
  unfold execution OneUseSource.execution
  rw [Procedure.steps_semantics]
  exact OneUseSourceExamples.run native oracle key sourceInput state trace request tail

theorem costed : (execution native oracle request).costed (start key sourceInput state trace request tail) =
    PMF.pure (OneUseSourceExamples.final key sourceInput state trace request tail, 2 * request.length + 47) := by
  unfold execution
  rw [OneUseSource.execution_cost]
  change (TimedExecution.eval (OneUseSource.step native OneUseSourceExamples.code oracle) (2 * request.length + 47) (OneUseSource.Control.source true key ⟨state, .running (OneUseSourceExamples.caller sourceInput request tail), trace⟩)).map _ = _
  rw [OneUseSourceExamples.run, PMF.pure_map]
end Foundation.OneUseIterationExamples
