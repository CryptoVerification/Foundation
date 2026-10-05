import Mathlib.Probability.Distributions.Uniform

/-! Finite probabilistic computations use Mathlib's `PMF` monad.  In particular,
successive `bind`s make fresh, independent draws.  The finite sampling API
requires a nonempty finite type; no sampling operation is attached to the
algebraic DDH parameters. -/

namespace Foundation.Probability

open scoped ENNReal

/-- A finite probabilistic computation. `PMF` supplies `pure`, `bind`, and `map`. -/
abbrev ProbComp (α : Type*) := PMF α

/-- Uniform sampling from a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : ProbComp α :=
  PMF.uniformOfFintype α

/-- A fair challenge bit. -/
noncomputable def sampleBit : ProbComp Bool := uniform Bool

/-- The probability of a result satisfying an event. -/
noncomputable def eventProb {α : Type*} (p : ProbComp α) (event : α → Prop) : ℝ≥0∞ :=
  p.toOuterMeasure {a | event a}

/-- Nonnegative absolute difference, expressed without signed subtraction in `ℝ≥0∞`. -/
noncomputable def probabilityGap (p q : ℝ≥0∞) : ℝ≥0∞ := max (p - q) (q - p)

/-- Binary guessing advantage is `|Pr[win] - 1/2|` (without a factor of two). -/
noncomputable def guessingAdvantage (success : ℝ≥0∞) : ℝ≥0∞ :=
  probabilityGap success (1 / 2)

end Foundation.Probability
