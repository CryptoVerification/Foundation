import Foundation.Crypto.Logic.Polygraph.GameProofShared

/-! Ordinary kernel/loss inference under exactly the finite condition set in
each judgment. Unlike the earlier ordinary model, no global supply of all
conditions is assumed. Operations consume ordinary comparisons directly;
no syntactic Cell is reconstructed or normalized in this interpretation. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation.FiniteOrdinary
open Foundation.Logic
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

theorem join {condition : Requirement → Prop} {first second : Finset Requirement}
    (left : Holds condition first) (right : Holds condition second) : Holds condition (first ∪ second) := by
  intro label member
  rcases Finset.mem_union.mp member with one | two
  · exact left label one
  · exact right label two

def Meaning {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators condition price)
    (claim : Claim layout) : Prop :=
  Holds condition claim.support →
    ∃ left : Holds condition (claim.left.needs layout), ∃ right : Holds condition (claim.right.needs layout),
      Comparison (evaluate model.base claim.left left) (evaluate model.base claim.right right)

noncomputable def interpretation {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators condition price) :
    Foundation.Logic.Model (theory layout relators) where
  Carrier := Meaning model
  operation := by
    intro rule children valid
    cases rule with
    | root label =>
      let left := valid.restrict (fun _ member => Finset.mem_union_left _ (Finset.mem_union_left _ member))
      let right := valid.restrict (fun _ member => Finset.mem_union_left _ (Finset.mem_union_right _ member))
      exact ⟨left, right, (model.comparison label left right
        (valid.restrict Finset.subset_union_right)).sound⟩
    | refl p => exact ⟨valid, valid, ⟨fun _ => rfl, rfl⟩⟩
    | symm p q support =>
      obtain ⟨left, right, comparison⟩ := children 0 valid
      exact ⟨right, left, ⟨fun state => (comparison.kernel_eq state).symm, comparison.loss_eq.symm⟩⟩
    | trans p q r first second =>
      obtain ⟨left, middleOne, one⟩ := children 0 (valid.restrict Finset.subset_union_left)
      obtain ⟨middleTwo, right, two⟩ := children 1 (valid.restrict Finset.subset_union_right)
      exact ⟨left, right, ⟨fun state => (one.kernel_eq state).trans (two.kernel_eq state),
        one.loss_eq.trans two.loss_eq⟩⟩
    | seq p p' q q' first second =>
      obtain ⟨left, left', one⟩ := children 0 (valid.restrict Finset.subset_union_left)
      obtain ⟨right, right', two⟩ := children 1 (valid.restrict Finset.subset_union_right)
      exact ⟨join left right, join left' right', (Cell4.seq (.generator one) (.generator two)).sound⟩
    | assoc p q r =>
      let first := valid.restrict (fun _ member => Finset.mem_union_left _ (Finset.mem_union_left _ member))
      let second := valid.restrict (fun _ member => Finset.mem_union_left _ (Finset.mem_union_right _ member))
      let third := valid.restrict Finset.subset_union_right
      exact ⟨join (join first second) third, join first (join second third),
        (Cell4.assoc (evaluate model.base p first) (evaluate model.base q second) (evaluate model.base r third)).sound⟩
    | leftUnit p =>
      refine ⟨?_, valid, (Cell4.leftUnit (evaluate model.base p valid)).sound⟩
      simpa only [Plan.needs, Finset.empty_union] using valid
    | rightUnit p =>
      refine ⟨?_, valid, (Cell4.rightUnit (evaluate model.base p valid)).sound⟩
      simpa only [Plan.needs, Finset.union_empty] using valid

theorem repaired {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {old updated : Requirement → Prop} {price : Budget → ENNReal} {model : HigherModel layout relators updated price}
    {claim : Claim layout} (evidence : Meaning model claim) (changed : Finset Requirement)
    (cached : Holds old claim.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh claim.support changed)) :
    ∃ left : Holds updated (claim.left.needs layout), ∃ right : Holds updated (claim.right.needs layout),
      Comparison (evaluate model.base claim.left left) (evaluate model.base claim.right right) :=
  evidence (repair cached unchanged rechecked)

theorem checked [DecidableEq Vertex] [DecidableEq Atom] [DecidableEq Budget]
    {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators condition price)
    {claim : Claim layout} (verified : Verified layout relators claim) : Meaning model claim :=
  (SharedInference.sound (interpretation model) verified.data verified.accepted).some

def compileAt [DecidableEq Vertex] [DecidableEq Atom] [DecidableEq Budget] [DecidableEq RelatorId]
    {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    (expected : Claim layout) (tree : SharedInference.Tree (Rule layout RelatorId)) :
    Option (Verified layout relators expected) := do
  let data ← SharedInference.compile (T := theory layout relators) tree
  if accepted : SharedInference.check data = some expected then pure ⟨data, accepted⟩ else none

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation.FiniteOrdinary
