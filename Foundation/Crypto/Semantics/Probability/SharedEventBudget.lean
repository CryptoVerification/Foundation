import Foundation.Crypto.Semantics.Probability.Facts
import Mathlib.Data.Finset.Lattice.Union

/-! A budget for events on ONE explicit joint probability space. Identical
labels may be charged once only because they denote the same predicate on
the same sample. This is not a rule for merging independent executions. -/
namespace Foundation.Probability.SharedEventBudget
open scoped ENNReal BigOperators
variable {World Label : Type} [DecidableEq Label]

def occurs (bad : Label → World → Prop) (support : Finset Label) (world : World) : Prop :=
  ∃ label ∈ support, bad label world

noncomputable def budget (price : Label → ℝ≥0∞) (support : Finset Label) : ℝ≥0∞ :=
  ∑ label ∈ support, price label

theorem union_bound (law : ProbComp World) (bad : Label → World → Prop) (support : Finset Label) :
    eventProb law (occurs bad support) ≤ budget (fun label => eventProb law (bad label)) support := by
  classical
  induction support using Finset.induction_on with
  | empty => simp [occurs, budget, eventProb]
  | @insert label support absent ih =>
      have same : occurs bad (insert label support) = (fun world => bad label world ∨ occurs bad support world) := by
        funext world; apply propext; simp [occurs]
      rw [same]
      exact (eventProb_or_le law _ _).trans (by
        simpa only [budget, Finset.sum_insert absent] using add_le_add le_rfl ih)

theorem covers (law : ProbComp World) (bad : Label → World → Prop) (support : Finset Label)
    (failure : World → Prop) (covered : ∀ world, failure world → occurs bad support world)
    (price : Label → ℝ≥0∞) (localBound : ∀ label ∈ support, eventProb law (bad label) ≤ price label) :
    eventProb law failure ≤ budget price support :=
  (eventProb_mono law covered).trans ((union_bound law bad support).trans (Finset.sum_le_sum localBound))

/-- Exact accounting for one event used in any positive number of places.
Sharing the lemma does not by itself change an occurrence-additive budget. -/
theorem repeated_budget (price : ℝ≥0∞) (n : Nat) :
    budget (fun _ : Unit => price) ({()} : Finset Unit) = price ∧
      (∑ _i : Fin n, price) = n * price := by
  simp [budget, nsmul_eq_mul]

theorem byte_strict (n : Nat) (many : 1 < n) :
    (256 : ℝ≥0∞)⁻¹ < n * (256 : ℝ≥0∞)⁻¹ := by
  have finite : (256 : ℝ≥0∞)⁻¹ < ⊤ := by norm_num
  have positive : 0 < (256 : ℝ≥0∞)⁻¹ := by norm_num
  have larger : (1 : ℝ≥0∞) < n := by exact_mod_cast many
  simpa only [one_mul] using ENNReal.mul_lt_mul_left positive.ne' finite.ne larger

end Foundation.Probability.SharedEventBudget
