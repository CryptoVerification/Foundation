import Mathlib.Data.Finset.Sort
import Foundation.Crypto.Logic.Polygraph.GameProofEncoding
import Foundation.Crypto.Logic.Polygraph.GameProofHigher
import Foundation.Logic.SharedInferenceEvaluation

/-! A finite-arity inference presentation of every constructor of Cell.
Rule payloads retain all boundary plans. It introduces no new higher root.
Raw reference certificates can therefore be checked at their actual typed
boundary, instead of using a fixed two-route benchmark grammar. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
open Foundation.Logic
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

structure Claim (layout : Layout Vertex Atom Requirement Budget) where
  source : Vertex
  target : Vertex
  left : Plan layout source target
  right : Plan layout source target
  support : Finset Requirement

deriving instance DecidableEq for Claim

inductive Rule (layout : Layout Vertex Atom Requirement Budget) (RelatorId : Type) where
  | root (label : RelatorId)
  | refl {a b} (p : Plan layout a b)
  | symm {a b} (p q : Plan layout a b) (support : Finset Requirement)
  | trans {a b} (p q r : Plan layout a b) (first second : Finset Requirement)
  | seq {a b c} (p p' : Plan layout a b) (q q' : Plan layout b c) (first second : Finset Requirement)
  | assoc {a b c d} (p : Plan layout a b) (q : Plan layout b c) (r : Plan layout c d)
  | leftUnit {a b} (p : Plan layout a b)
  | rightUnit {a b} (p : Plan layout a b)

deriving instance DecidableEq for Rule

abbrev theory (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout) : Presentation where
  Judgment := Claim layout
  Rule := Rule layout RelatorId
  arity := fun | .root .. | .refl .. | .assoc .. | .leftUnit .. | .rightUnit .. => 0 | .symm .. => 1 | .trans .. | .seq .. => 2
  premise := fun
    | .root .. | .refl .. | .assoc .. | .leftUnit .. | .rightUnit .. => Fin.elim0
    | .symm p q support => fun _ => ⟨_, _, p, q, support⟩
    | .trans p q r first second => Fin.cases ⟨_, _, p, q, first⟩ (fun _ => ⟨_, _, q, r, second⟩)
    | .seq p p' q q' first second => Fin.cases ⟨_, _, p, p', first⟩ (fun _ => ⟨_, _, q, q', second⟩)
  conclusion := fun
    | .root label => ⟨_, _, (relators label).left, (relators label).right,
        (relators label).left.needs layout ∪ (relators label).right.needs layout ∪ (relators label).needs⟩
    | .refl p => ⟨_, _, p, p, p.needs layout⟩
    | .symm p q support => ⟨_, _, q, p, support⟩
    | .trans p _ r first second => ⟨_, _, p, r, first ∪ second⟩
    | .seq p p' q q' first second => ⟨_, _, .seq p q, .seq p' q', first ∪ second⟩
    | .assoc p q r => ⟨_, _, .seq (.seq p q) r, .seq p (.seq q r), p.needs layout ∪ q.needs layout ∪ r.needs layout⟩
    | .leftUnit p => ⟨_, _, .seq (.identity _) p, p, p.needs layout⟩
    | .rightUnit p => ⟨_, _, .seq p (.identity _), p, p.needs layout⟩

def geometric (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout) :
    Foundation.Logic.Model (theory layout relators) where
  Carrier := fun claim => {cell : Cell layout relators claim.left claim.right // cell.needs layout relators = claim.support}
  operation := fun rule children => match rule with
    | .root label => ⟨.rule label, rfl⟩
    | .refl p => ⟨.refl p, rfl⟩
    | .symm _ _ _ => ⟨.symm (children 0).1, (children 0).2⟩
    | .trans .. => ⟨.trans (children 0).1 (children 1).1, by
        change (children 0).1.needs layout relators ∪ (children 1).1.needs layout relators = _
        rw [(children 0).2, (children 1).2]
        rfl⟩
    | .seq .. => ⟨.seq (children 0).1 (children 1).1, by
        change (children 0).1.needs layout relators ∪ (children 1).1.needs layout relators = _
        rw [(children 0).2, (children 1).2]
        rfl⟩
    | .assoc p q r => ⟨.assoc p q r, rfl⟩
    | .leftUnit p => ⟨.leftUnit p, rfl⟩
    | .rightUnit p => ⟨.rightUnit p, rfl⟩

def toTree {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout} :
    {a b : Vertex} → {p q : Plan layout a b} → Cell layout relators p q →
    SharedInference.Tree (Rule layout RelatorId)
  | _, _, _, _, .rule label => .node (.root label) []
  | _, _, _, _, .refl p => .node (.refl p) []
  | _, _, _, _, @Cell.symm _ _ _ _ _ _ _ _ _ p q child => .node (.symm p q (child.needs layout relators)) [toTree child]
  | _, _, _, _, @Cell.trans _ _ _ _ _ _ _ _ _ p q r first second =>
      .node (.trans p q r (first.needs layout relators) (second.needs layout relators)) [toTree first, toTree second]
  | _, _, _, _, @Cell.seq _ _ _ _ _ _ _ _ _ _ p p' q q' first second =>
      .node (.seq p p' q q' (first.needs layout relators) (second.needs layout relators)) [toTree first, toTree second]
  | _, _, _, _, .assoc p q r => .node (.assoc p q r) []
  | _, _, _, _, .leftUnit p => .node (.leftUnit p) []
  | _, _, _, _, .rightUnit p => .node (.rightUnit p) []

def render [Repr Vertex] [Repr Atom] [Repr Requirement] [LinearOrder Requirement] [Repr RelatorId] {layout : Layout Vertex Atom Requirement Budget} :
    Rule layout RelatorId → String
  | .root label => "root:" ++ reprStr label
  | .refl p => "refl:" ++ reprStr p.shape
  | .symm p q support => "symm:" ++ reprStr (p.shape, q.shape, support.sort (· ≤ ·))
  | .trans p q r first second => "trans:" ++ reprStr (p.shape, q.shape, r.shape, first.sort (· ≤ ·), second.sort (· ≤ ·))
  | .seq p p' q q' first second => "seq:" ++ reprStr (p.shape, p'.shape, q.shape, q'.shape, first.sort (· ≤ ·), second.sort (· ≤ ·))
  | .assoc p q r => "assoc:" ++ reprStr (p.shape, q.shape, r.shape)
  | .leftUnit p => "leftUnit:" ++ reprStr p.shape
  | .rightUnit p => "rightUnit:" ++ reprStr p.shape

theorem checked [DecidableEq Vertex] [DecidableEq Atom] [DecidableEq Budget]
    (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    (certificate : SharedInference.Certificate (theory layout relators)) {a b : Vertex} (p q : Plan layout a b) (support : Finset Requirement)
    (accepted : SharedInference.check certificate = some ⟨a, b, p, q, support⟩) :
    Nonempty {cell : Cell layout relators p q // cell.needs layout relators = support} :=
  SharedInference.sound (geometric layout relators) certificate accepted

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
