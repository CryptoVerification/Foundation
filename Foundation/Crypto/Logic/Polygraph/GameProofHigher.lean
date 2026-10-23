import Foundation.Crypto.Logic.Polygraph.GameProofInterpretation

/-! Higher proof diagrams with their own condition dependencies. A named
relator has two directed plans, balanced symbolic charges, and additional
conditions needed for its kernel comparison. Interior conditions are retained
under higher pasting, even when absent from both outer boundary plans. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Probability
open scoped ENNReal
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

structure Relator (layout : Layout Vertex Atom Requirement Budget) where
  source : Vertex
  target : Vertex
  left : Plan layout source target
  right : Plan layout source target
  needs : Finset Requirement
  balanced : left.charges layout = right.charges layout

inductive Cell (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout) :
    {a b : Vertex} → Plan layout a b → Plan layout a b → Type where
  | rule (label : RelatorId) : Cell layout relators (relators label).left (relators label).right
  | refl {a b} (plan : Plan layout a b) : Cell layout relators plan plan
  | symm {a b} {p q : Plan layout a b} : Cell layout relators p q → Cell layout relators q p
  | trans {a b} {p q r : Plan layout a b} : Cell layout relators p q → Cell layout relators q r → Cell layout relators p r
  | seq {a b c} {p p' : Plan layout a b} {q q' : Plan layout b c} :
      Cell layout relators p p' → Cell layout relators q q' → Cell layout relators (.seq p q) (.seq p' q')
  | assoc {a b c d} (p : Plan layout a b) (q : Plan layout b c) (r : Plan layout c d) :
      Cell layout relators (.seq (.seq p q) r) (.seq p (.seq q r))
  | leftUnit {a b} (p : Plan layout a b) : Cell layout relators (.seq (.identity a) p) p
  | rightUnit {a b} (p : Plan layout a b) : Cell layout relators (.seq p (.identity b)) p

def Cell.needs (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout) :
    {a b : Vertex} → {p q : Plan layout a b} → Cell layout relators p q → Finset Requirement
  | _, _, _, _, .rule label => (relators label).left.needs layout ∪ (relators label).right.needs layout ∪ (relators label).needs
  | _, _, _, _, .refl plan => plan.needs layout
  | _, _, _, _, .symm child => child.needs layout relators
  | _, _, _, _, .trans first second => first.needs layout relators ∪ second.needs layout relators
  | _, _, _, _, .seq first second => first.needs layout relators ∪ second.needs layout relators
  | _, _, _, _, .assoc p q r => p.needs layout ∪ q.needs layout ∪ r.needs layout
  | _, _, _, _, .leftUnit p => p.needs layout
  | _, _, _, _, .rightUnit p => p.needs layout

theorem Cell.endpoint_needs (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) :
    p.needs layout ⊆ cell.needs layout relators ∧ q.needs layout ⊆ cell.needs layout relators := by
  induction cell with
  | rule label =>
    exact ⟨fun _ member => Finset.mem_union_left _ (Finset.mem_union_left _ member),
      fun _ member => Finset.mem_union_left _ (Finset.mem_union_right _ member)⟩
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ first second =>
    exact ⟨fun _ member => Finset.mem_union_left _ (first.1 member),
      fun _ member => Finset.mem_union_right _ (second.2 member)⟩
  | seq _ _ first second =>
    constructor
    · intro label member
      rcases Finset.mem_union.mp member with left | right
      · exact Finset.mem_union_left _ (first.1 left)
      · exact Finset.mem_union_right _ (second.1 right)
    · intro label member
      rcases Finset.mem_union.mp member with left | right
      · exact Finset.mem_union_left _ (first.2 left)
      · exact Finset.mem_union_right _ (second.2 right)
  | assoc => simp only [Plan.needs, Cell.needs, Finset.union_assoc]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | leftUnit => simp only [Plan.needs, Cell.needs, Finset.empty_union]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | rightUnit => simp only [Plan.needs, Cell.needs, Finset.union_empty]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

omit [DecidableEq Requirement] in
theorem Cell.charge_eq (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) : p.charges layout = q.charges layout := by
  induction cell with
  | rule label => exact (relators label).balanced
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | seq _ _ first second => exact congrArg₂ (fun (x y : Multiset Budget) => x + y) first second
  | assoc => exact add_assoc _ _ _
  | leftUnit => exact zero_add _
  | rightUnit => exact add_zero _

omit [DecidableEq Requirement] in
theorem Cell.totalCharge_eq (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (price : Budget → ℝ≥0∞) :
    totalCharge price (p.charges layout) = totalCharge price (q.charges layout) :=
  congrArg (totalCharge price) (cell.charge_eq layout relators)

def Cell.fresh (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (changed : Finset Requirement) : Finset Requirement :=
  Requirements.fresh (cell.needs layout relators) changed

def Cell.checkReuse (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (changed : Finset Requirement) : Bool :=
  Requirements.checkReuse (cell.needs layout relators) changed

/-- A local rule's extra conditions must justify equality of conditional
kernels and losses in the existing directed semantics. Marginals alone do not
suffice. Conditions outside the named finite sets are not supplied. -/
structure HigherModel (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    (condition : Requirement → Prop) (price : Budget → ℝ≥0∞) where
  base : Model layout condition price
  comparison : ∀ label (left : Holds condition ((relators label).left.needs layout))
    (right : Holds condition ((relators label).right.needs layout)), Holds condition ((relators label).needs) →
    Cell4 (evaluate base (relators label).left left) (evaluate base (relators label).right right)

noncomputable def evaluateCell {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ℝ≥0∞} (model : HigherModel layout relators condition price) :
    {a b : Vertex} → {p q : Plan layout a b} → (cell : Cell layout relators p q) →
    (proof : Holds condition (cell.needs layout relators)) →
    Cell4 (evaluate model.base p (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base q (proof.restrict (cell.endpoint_needs layout relators).2))
  | _, _, _, _, .rule label, proof => model.comparison label
      (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_left _ member)))
      (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_right _ member)))
      (fun _ member => proof _ (Finset.mem_union_right _ member))
  | _, _, _, _, .refl plan, proof => .refl (evaluate model.base plan proof)
  | _, _, _, _, .symm child, proof => (evaluateCell model child proof).symm
  | _, _, _, _, .trans first second, proof => .trans
      (evaluateCell model first (proof.restrict Finset.subset_union_left))
      (evaluateCell model second (proof.restrict Finset.subset_union_right))
  | _, _, _, _, .seq first second, proof => .seq
      (evaluateCell model first (proof.restrict Finset.subset_union_left))
      (evaluateCell model second (proof.restrict Finset.subset_union_right))
  | _, _, _, _, .assoc p q r, proof => .assoc
      (evaluate model.base p (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_left _ member))))
      (evaluate model.base q (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_right _ member))))
      (evaluate model.base r (fun _ member => proof _ (Finset.mem_union_right _ member)))
  | _, _, _, _, .leftUnit p, proof => .leftUnit (evaluate model.base p proof)
  | _, _, _, _, .rightUnit p, proof => .rightUnit (evaluate model.base p proof)

theorem evaluateCell_sound {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ℝ≥0∞} (model : HigherModel layout relators condition price)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q)
    (proof : Holds condition (cell.needs layout relators)) :
    Comparison (evaluate model.base p (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base q (proof.restrict (cell.endpoint_needs layout relators).2)) :=
  (evaluateCell model cell proof).sound

/-- Cache repair also includes conditions used only inside the higher diagram.
The updated model may change games, kernels and error prices; the symbolic
layout and relator catalog remain fixed. -/
theorem repaired_comparison {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {old updated : Requirement → Prop} {price : Budget → ℝ≥0∞} (model : HigherModel layout relators updated price)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (changed : Finset Requirement)
    (cached : Holds old (cell.needs layout relators))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (cell.fresh layout relators changed)) :
    let proof := repair cached unchanged rechecked
    Comparison (evaluate model.base p (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base q (proof.restrict (cell.endpoint_needs layout relators).2)) :=
  evaluateCell_sound model cell (repair cached unchanged rechecked)

/-- The repaired higher diagram also certifies an event-probability bound at
the CURRENT prices. Old numerical prices are not silently reused. -/
theorem repaired_bound {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {old updated : Requirement → Prop} {price : Budget → ℝ≥0∞} (model : HigherModel layout relators updated price)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (changed : Finset Requirement)
    (cached : Holds old (cell.needs layout relators))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (cell.fresh layout relators changed)) :
    probabilityGap (model.base.game a).probability (model.base.game b).probability ≤ totalCharge price (p.charges layout) :=
  evaluate_sound model.base p ((repair cached unchanged rechecked).restrict (cell.endpoint_needs layout relators).1)

/-- With an empty generated fresh set, no new condition proof is requested. -/
theorem reused_comparison {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {old updated : Requirement → Prop} {price : Budget → ℝ≥0∞} (model : HigherModel layout relators updated price)
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) (changed : Finset Requirement)
    (cached : Holds old (cell.needs layout relators))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (accepted : cell.checkReuse layout relators changed = true) :
    let proof := reuse cached unchanged accepted
    Comparison (evaluate model.base p (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base q (proof.restrict (cell.endpoint_needs layout relators).2)) :=
  evaluateCell_sound model cell (reuse cached unchanged accepted)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
