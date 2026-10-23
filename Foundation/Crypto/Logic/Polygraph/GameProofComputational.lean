import Foundation.Crypto.Logic.Polygraph.GameProofNormalization
import Foundation.Crypto.Logic.Polygraph.ComputationalComparison
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! A second interpretation of the same directed condition-bearing proof
syntax, now in certified computational reductions. Higher cells must preserve
the actual reduction outputs, programs, resources and loss functions.
Symbolic additive charge bags alone do NOT determine nonlinear computational
loss transformers. No statistical coupling is inferred from this model. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Computational
open General
open scoped ENNReal
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

structure Model (K : CodeSystem) (layout : Layout Vertex Atom Requirement Budget) (condition : Requirement → Prop) where
  machine : Vertex → K.Machine
  object : ∀ vertex, General.SecurityObject.{0, 0} K (machine vertex)
  atom : ∀ label, Holds condition (layout.needs label) →
    General.CertifiedReduction (object (layout.source label)) (object (layout.target label))

def evaluate {K : CodeSystem} {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    (model : Model K layout condition) : {a b : Vertex} → (plan : Plan layout a b) →
    Holds condition (plan.needs layout) → General.CertifiedReduction (model.object a) (model.object b)
  | _, _, .identity vertex, _ => .id (model.object vertex)
  | _, _, .atom label, proof => model.atom label proof
  | _, _, .seq first second, proof =>
      (evaluate model first (proof.restrict Finset.subset_union_left)).comp
        (evaluate model second (proof.restrict Finset.subset_union_right))

structure HigherModel (K : CodeSystem) (layout : Layout Vertex Atom Requirement Budget)
    (relators : RelatorId → Relator layout) (condition : Requirement → Prop) where
  base : Model K layout condition
  comparison : ∀ label (left : Holds condition ((relators label).left.needs layout))
    (right : Holds condition ((relators label).right.needs layout)), Holds condition ((relators label).needs) →
    General.CertifiedComparison (evaluate base (relators label).left left) (evaluate base (relators label).right right)

theorem evaluateCell {K : CodeSystem} {layout : Layout Vertex Atom Requirement Budget}
    {relators : RelatorId → Relator layout} {condition : Requirement → Prop}
    (model : HigherModel K layout relators condition) : {a b : Vertex} → {first second : Plan layout a b} →
    (cell : Cell layout relators first second) → (proof : Holds condition (cell.needs layout relators)) →
    General.CertifiedComparison
      (evaluate model.base first (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base second (proof.restrict (cell.endpoint_needs layout relators).2))
  | _, _, _, _, .rule label, proof => model.comparison label
      (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_left _ member)))
      (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_right _ member)))
      (fun _ member => proof _ (Finset.mem_union_right _ member))
  | _, _, _, _, .refl plan, proof => .refl (evaluate model.base plan proof)
  | _, _, _, _, .symm child, proof => (evaluateCell model child proof).symm
  | _, _, _, _, .trans first second, proof =>
      (evaluateCell model first (proof.restrict Finset.subset_union_left)).trans
        (evaluateCell model second (proof.restrict Finset.subset_union_right))
  | _, _, _, _, .seq first second, proof =>
      (evaluateCell model first (proof.restrict Finset.subset_union_left)).comp
        (evaluateCell model second (proof.restrict Finset.subset_union_right))
  | _, _, _, _, .assoc p q r, proof => .assoc
      (evaluate model.base p (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_left _ member))))
      (evaluate model.base q (fun _ member => proof _ (Finset.mem_union_left _ (Finset.mem_union_right _ member))))
      (evaluate model.base r (fun _ member => proof _ (Finset.mem_union_right _ member)))
  | _, _, _, _, .leftUnit plan, proof => .leftUnit (evaluate model.base plan proof)
  | _, _, _, _, .rightUnit plan, proof => .rightUnit (evaluate model.base plan proof)

theorem secure {K : CodeSystem} {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    (model : Model K layout condition) {a b : Vertex} (plan : Plan layout a b)
    (proof : Holds condition (plan.needs layout)) (family)
    (hypothesis : (model.object b).Secure ((evaluate model plan proof).reduction.mapFamily family)) :
    (model.object a).Secure family :=
  (evaluate model plan proof).secure family hypothesis

theorem bounded {K : CodeSystem} {layout : Layout Vertex Atom Requirement Budget} {condition : Requirement → Prop}
    (model : Model K layout condition) {a b : Vertex} (plan : Plan layout a b)
    (proof : Holds condition (plan.needs layout)) (family ε)
    (hypothesis : (model.object b).Bounded ((evaluate model plan proof).reduction.mapFamily family) ε) :
    (model.object a).Bounded family (fun n => (evaluate model plan proof).reduction.loss.eval n (ε n)) :=
  (evaluate model plan proof).bounded family ε hypothesis

theorem repaired_comparison {K : CodeSystem} {layout : Layout Vertex Atom Requirement Budget}
    {relators : RelatorId → Relator layout} {old updated : Requirement → Prop}
    (model : HigherModel K layout relators updated) {a b : Vertex} {first second : Plan layout a b}
    (cell : Cell layout relators first second) (changed : Finset Requirement)
    (cached : Holds old (cell.needs layout relators))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (cell.fresh layout relators changed)) :
    let proof := repair cached unchanged rechecked
    General.CertifiedComparison
      (evaluate model.base first (proof.restrict (cell.endpoint_needs layout relators).1))
      (evaluate model.base second (proof.restrict (cell.endpoint_needs layout relators).2)) :=
  evaluateCell model cell (repair cached unchanged rechecked)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Computational
