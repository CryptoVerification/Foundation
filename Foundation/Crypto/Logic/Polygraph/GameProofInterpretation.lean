import Foundation.Crypto.Logic.Polygraph.GameProofRequirements
import Foundation.Crypto.Logic.Polygraph.GameCoherence

/-! Interpret the pure condition/charge plans in the existing directed
conditional-kernel game semantics. Only conditions actually declared by the
plan are supplied. Realizers and their loss equations are checked Lean data. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Probability
open scoped ENNReal
variable {Vertex Atom Requirement Budget : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

noncomputable def totalCharge (price : Budget → ℝ≥0∞) (charges : Multiset Budget) : ℝ≥0∞ :=
  (charges.map price).sum

theorem totalCharge_add (price : Budget → ℝ≥0∞) (one two : Multiset Budget) :
    totalCharge price (one + two) = totalCharge price one + totalCharge price two := by
  simp only [totalCharge, Multiset.map_add, Multiset.sum_add]

/-- Atomic realizers may be exact or statistical paths. There is no inverse
constructor for stochastic execution. Conditions and prices can vary in an
external parameter by supplying the corresponding model. -/
structure Model (layout : Layout Vertex Atom Requirement Budget) (condition : Requirement → Prop)
    (price : Budget → ℝ≥0∞) where
  game : Vertex → Observed.{0}
  atom : ∀ label, Holds condition (layout.needs label) → Path (game (layout.source label)) (game (layout.target label))
  atom_loss : ∀ label proof, (atom label proof).loss = totalCharge price (layout.charges label)

noncomputable def evaluate {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    {price : Budget → ℝ≥0∞} (model : Model layout condition price) : {a b : Vertex} →
    (plan : Plan layout a b) → Holds condition (plan.needs layout) → Path (model.game a) (model.game b)
  | _, _, .identity vertex, _ => .identity (model.game vertex)
  | _, _, .atom label, proof => model.atom label proof
  | _, _, .seq first second, proof => .seq
      (evaluate model first (proof.restrict (Finset.subset_union_left)))
      (evaluate model second (proof.restrict (Finset.subset_union_right)))

theorem evaluate_loss {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    {price : Budget → ℝ≥0∞} (model : Model layout condition price) {a b : Vertex}
    (plan : Plan layout a b) (proof : Holds condition (plan.needs layout)) :
    (evaluate model plan proof).loss = totalCharge price (plan.charges layout) := by
  induction plan with
  | identity => simp only [evaluate, Path.loss, Plan.charges, totalCharge, Multiset.map_zero, Multiset.sum_zero]
  | atom label => exact model.atom_loss label proof
  | seq first second ihFirst ihSecond =>
    simp only [evaluate, Path.loss, Plan.charges, totalCharge_add]
    exact congrArg₂ (fun (x y : ℝ≥0∞) => x + y) (ihFirst _) (ihSecond _)

theorem evaluate_sound {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    {price : Budget → ℝ≥0∞} (model : Model layout condition price) {a b : Vertex}
    (plan : Plan layout a b) (proof : Holds condition (plan.needs layout)) :
    probabilityGap (model.game a).probability (model.game b).probability ≤ totalCharge price (plan.charges layout) := by
  rw [← evaluate_loss model plan proof]
  exact (evaluate model plan proof).sound

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
