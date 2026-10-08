import Foundation.Crypto.Semantics.Oracle.Reification
import Foundation.Crypto.Semantics.Simulation

/-! The existing finite source-machine evaluator is a generic timed
transition system, with genuine source termination as an absorbing boundary.
Fuel exhaustion remains distinct from source-machine termination. -/
namespace CryptoOracle.Interactive.Reification
open Foundation.Probability
universe u

noncomputable def timedStep {State : Type u} (code : Code) (oracle : BitOracle State)
    (frame : Configuration State) : PMF (Configuration State) :=
  if terminal frame.control then PMF.pure frame else perform code oracle frame

theorem timed_eval_eq {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (frame : Configuration State) :
    TimedExecution.eval (timedStep code oracle) fuel frame = eval code oracle fuel frame := by
  induction fuel generalizing frame with
  | zero => simp [TimedExecution.eval, eval_zero]
  | succ fuel ih =>
      rw [TimedExecution.eval]
      by_cases ht : terminal frame.control = true
      · simp [timedStep, ht, ih, eval_terminal]
      · simp only [timedStep, ht, Bool.false_eq_true, ↓reduceIte]
        simp only [eval, ht, Bool.false_eq_true, ↓reduceIte, step_eq_perform]
        congr 1
        funext next
        exact ih next

end CryptoOracle.Interactive.Reification
