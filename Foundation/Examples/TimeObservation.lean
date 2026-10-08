import Foundation.Crypto.Semantics.Probability.ObserverBound

/-! A regression for the boundary between output secrecy and time secrecy.
These distributions are mathematical examples, not compiled programs. -/
namespace Foundation.Examples.TimeObservation
open Foundation.Probability
open scoped ENNReal

noncomputable def left : PMF (Bool × Nat) := PMF.pure (false, 0)
noncomputable def right : PMF (Bool × Nat) := PMF.pure (false, 1)

noncomputable def detectsZeroTime (result : Bool × Nat) : PMF Bool :=
  PMF.pure (decide (result.2 = 0))

theorem same_output : left.map Prod.fst = right.map Prod.fst := by
  simp [left, right, PMF.pure_map]

theorem time_gap : observerGap left right detectsZeroTime = 1 := by
  simp [observerGap, left, right, detectsZeroTime, eventProb, probabilityGap]

theorem no_zero_joint_bound : ¬ ObserverBound (fun _ => True) left right 0 := by
  intro h
  have hGap := h detectsZeroTime trivial
  rw [time_gap] at hGap
  exact (by simp : ¬ (1 : ℝ≥0∞) ≤ 0) hGap

end Foundation.Examples.TimeObservation
