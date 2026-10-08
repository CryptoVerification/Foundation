import Foundation.Crypto.Semantics.TimedExecution

/-! Full-state distributional simulation of arbitrary probabilistic machines.
An observation may forget private state; it does not run as a machine step. -/
namespace Foundation.Probability.TimedExecution
universe u v
variable {Source : Type u} {Target : Type v}

theorem eval_map (source : Source → PMF Source) (target : Target → PMF Target)
    (view : Source → Target)
    (hStep : ∀ state, (source state).map view = target (view state))
    (fuel : Nat) (start : Source) :
    (eval source fuel start).map view = eval target fuel (view start) := by
  induction fuel generalizing start with
  | zero => simp [eval, PMF.pure_map]
  | succ fuel ih =>
      rw [eval, eval, PMF.map_bind, ← hStep start, PMF.bind_map]
      congr 1
      funext next
      exact ih next

end Foundation.Probability.TimedExecution
