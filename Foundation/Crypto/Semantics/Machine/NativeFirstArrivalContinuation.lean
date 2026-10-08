import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Embed a terminating native component into a continuing transition
system. Only pre-return transitions must agree. The actual first-return
cost law, physical return state and source budget are retained unchanged. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {Target : Type w} (P : NativeComponent Input Output)
    (targetStep : Target → PMF Target) (boundary : Target → Bool) (embed : Configuration → Target)
    (hBoundary : ∀ state, boundary (embed state) = state.halted)
    (hStep : ∀ state, state.halted = false → targetStep (embed state) = (stepPMF P.procedure.code state).map embed)

noncomputable def continueIn : TimedExecution.Procedure targetStep Input Configuration :=
  P.firstArrival.procedure.execution.liftBoundary Configuration.halted P.firstArrival.halted
    (fun state h => by simp [stepPMF, next, h]) (fun _ state => state) (fun _ _ => rfl)
    targetStep boundary embed hBoundary hStep

theorem continueIn_entry (input : Input) :
    (P.continueIn targetStep boundary embed hBoundary hStep).entry input = embed (P.procedure.execution.entry input) := rfl

theorem continueIn_exit (input : Input) (state : Configuration) :
    (P.continueIn targetStep boundary embed hBoundary hStep).exit input state = embed state := rfl

theorem continueIn_budget (input : Input) :
    (P.continueIn targetStep boundary embed hBoundary hStep).budget input = P.procedure.execution.budget input := rfl

theorem continueIn_semantics (input : Input) :
    (P.continueIn targetStep boundary embed hBoundary hStep).semantics input =
      (P.procedure.execution.semantics input).map (P.procedure.execution.exit input) := rfl

theorem continueIn_costed (input : Input) :
    (P.continueIn targetStep boundary embed hBoundary hStep).costed input =
      P.firstArrival.procedure.execution.costed input := by
  change (runToBoundary (stepPMF P.procedure.code) Configuration.halted (P.procedure.execution.budget input)
    (P.procedure.execution.entry input)).map (fun result => (result.1, result.2)) = _
  rw [P.firstArrival_costed]
  exact PMF.map_id _

end Machine.NativeComponent
