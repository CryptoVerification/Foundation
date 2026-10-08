import Foundation.Crypto.Semantics.Machine.Execution
import Foundation.Crypto.Semantics.Procedure

/-! Finite native code implementing a composable whole-configuration contract.
An entry is a precondition on the physical tapes, not a free preparation step. -/
namespace Machine
open Foundation.Probability
open TimedExecution
universe u v

theorem timed_eval_eq (code : Program) (start : Configuration) (fuel : Nat) :
    TimedExecution.eval (stepPMF code) fuel start = evalConfigWithin code start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      conv_rhs => rw [show fuel + 1 = 1 + fuel by omega, evalConfigWithin_add]
      simp only [evalConfigWithin, PMF.pure_bind, TimedExecution.eval]
      congr 1
      funext next
      exact ih next

structure Procedure (Input : Type u) (Output : Type v) where
  code : Program
  execution : TimedExecution.Procedure (stepPMF code) Input Output

namespace Procedure
variable {Input : Type u} {Output : Type v}

noncomputable def ofFixed (code : Program) (entry : Input → Configuration)
    (exit : Input → Output → Configuration) (semantics : Input → PMF Output) (duration : Input → Nat)
    (run : ∀ input, evalConfigWithin code (entry input) (duration input) = (semantics input).map (exit input)) :
    Procedure Input Output where
  code := code
  execution := TimedExecution.Procedure.ofFixed (stepPMF code) entry exit semantics duration
    (fun input => (timed_eval_eq code (entry input) (duration input)).trans (run input))

/-- Observe the actual physical endpoints after native halt. -/
theorem final_run (P : Procedure Input Output) (input : Input)
    (hHalt : ∀ output ∈ (P.execution.semantics input).support, (P.execution.exit input output).halted = true)
    (horizon : Nat) (hBudget : P.execution.budget input ≤ horizon) :
    evalConfigWithin P.code (P.execution.entry input) horizon =
      (P.execution.semantics input).map (P.execution.exit input) := by
  rw [← timed_eval_eq]
  apply P.execution.final_run input _ horizon hBudget
  intro output hOutput
  simp [stepPMF, next, hHalt output hOutput]

end Procedure
end Machine
