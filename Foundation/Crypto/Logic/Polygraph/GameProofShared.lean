import Foundation.Crypto.Logic.Polygraph.GameProofPresentation
import Foundation.Crypto.Logic.Polygraph.GameProofComputational
import Foundation.Logic.SharedInferenceCompilation

/-! Checked shared outputs for actual Cell diagrams, including exact declared
interior support. A successful output carries the checker's acceptance proof.
Both probabilistic and computational semantics are recovered from that proof;
the interning producer is not trusted and may return failure. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
open Foundation.Logic
variable {Vertex Atom Requirement Budget RelatorId : Type}
variable [DecidableEq Vertex] [DecidableEq Atom] [DecidableEq Requirement] [DecidableEq Budget]
set_option backward.isDefEq.respectTransparency false

structure Verified (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    (claim : Claim layout) where
  data : SharedInference.Certificate (theory layout relators)
  accepted : SharedInference.check data = some claim

def compileMode [DecidableEq RelatorId] {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {a b : Vertex} {p q : Plan layout a b} (sharing : Bool) (cell : Cell layout relators p q) :
    Option (Verified layout relators ⟨a, b, p, q, cell.needs layout relators⟩) := do
  let data ← if sharing then SharedInference.compile (T := theory layout relators) (toTree cell)
    else SharedInference.compileUnshared (T := theory layout relators) (toTree cell)
  if accepted : SharedInference.check data = some ⟨a, b, p, q, cell.needs layout relators⟩ then
    pure ⟨data, accepted⟩
  else none

def compile [DecidableEq RelatorId] {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) := compileMode true cell

noncomputable def ordinary {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators condition price)
    (valid : ∀ label, condition label) : Foundation.Logic.Model (theory layout relators) where
  Carrier := fun claim => Comparison
    (evaluate model.base claim.left (fun label _ => valid label))
    (evaluate model.base claim.right (fun label _ => valid label))
  operation := fun rule children => match rule with
    | .root label => (model.comparison label (fun label _ => valid label)
        (fun label _ => valid label) (fun label _ => valid label)).sound
    | .refl _ => ⟨fun _ => rfl, rfl⟩
    | .symm .. => ⟨fun state => ((children 0).kernel_eq state).symm, (children 0).loss_eq.symm⟩
    | .trans .. => ⟨fun state => ((children 0).kernel_eq state).trans ((children 1).kernel_eq state),
        (children 0).loss_eq.trans (children 1).loss_eq⟩
    | .seq .. => (Cell4.seq (.generator (children 0)) (.generator (children 1))).sound
    | .assoc p q r => (Cell4.assoc
        (evaluate model.base p (fun label _ => valid label))
        (evaluate model.base q (fun label _ => valid label))
        (evaluate model.base r (fun label _ => valid label))).sound
    | .leftUnit p => (Cell4.leftUnit (evaluate model.base p (fun label _ => valid label))).sound
    | .rightUnit p => (Cell4.rightUnit (evaluate model.base p (fun label _ => valid label))).sound

theorem Verified.diagram {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {claim : Claim layout} (verified : Verified layout relators claim) :
    Nonempty {cell : Cell layout relators claim.left claim.right // cell.needs layout relators = claim.support} :=
  SharedInference.sound (geometric layout relators) verified.data verified.accepted

theorem Verified.probabilistic {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {condition : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators condition price)
    {claim : Claim layout} (verified : Verified layout relators claim) (valid : Holds condition claim.support) :
    ∃ left : Holds condition (claim.left.needs layout), ∃ right : Holds condition (claim.right.needs layout),
      Comparison (evaluate model.base claim.left left) (evaluate model.base claim.right right) := by
  obtain ⟨cell, support⟩ := verified.diagram
  have proof : Holds condition (cell.needs layout relators) := by rw [support]; exact valid
  exact ⟨proof.restrict (cell.endpoint_needs layout relators).1, proof.restrict (cell.endpoint_needs layout relators).2,
    evaluateCell_sound model cell proof⟩

theorem Verified.computational {K : General.CodeSystem} {layout : Layout Vertex Atom Requirement Budget}
    {relators : RelatorId → Relator layout} {condition : Requirement → Prop}
    (model : Computational.HigherModel K layout relators condition) {claim : Claim layout}
    (verified : Verified layout relators claim) (valid : Holds condition claim.support) :
    ∃ left : Holds condition (claim.left.needs layout), ∃ right : Holds condition (claim.right.needs layout),
      General.CertifiedComparison (Computational.evaluate model.base claim.left left)
        (Computational.evaluate model.base claim.right right) := by
  obtain ⟨cell, support⟩ := verified.diagram
  have proof : Holds condition (cell.needs layout relators) := by rw [support]; exact valid
  exact ⟨proof.restrict (cell.endpoint_needs layout relators).1, proof.restrict (cell.endpoint_needs layout relators).2,
    Computational.evaluateCell model cell proof⟩

theorem Verified.repaired {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {old updated : Requirement → Prop} {price : Budget → ENNReal} (model : HigherModel layout relators updated price)
    {claim : Claim layout} (verified : Verified layout relators claim) (changed : Finset Requirement)
    (cached : Holds old claim.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh claim.support changed)) :
    ∃ left : Holds updated (claim.left.needs layout), ∃ right : Holds updated (claim.right.needs layout),
      Comparison (evaluate model.base claim.left left) (evaluate model.base claim.right right) :=
  verified.probabilistic model (repair cached unchanged rechecked)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
