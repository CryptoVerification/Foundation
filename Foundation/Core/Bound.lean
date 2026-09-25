import Foundation.Core.Goal

open scoped ENNReal

/-- A monotone upper bound on an advantage, parameterized by the security parameter. -/
structure AdvantageBound where
  eval : Nat → ℝ≥0∞ → ℝ≥0∞
  monotone : ∀ n, Monotone (eval n)

namespace AdvantageBound

/-- The bound that leaves the advantage unchanged. -/
def id : AdvantageBound where
  eval := fun _ x => x
  monotone := by
    intro _ _ _ h
    exact h

/-- Apply `g` first, then `f`. -/
def comp (f g : AdvantageBound) : AdvantageBound where
  eval := fun n x => f.eval n (g.eval n x)
  monotone := by
    intro n x y h
    exact f.monotone n (g.monotone n h)

end AdvantageBound
