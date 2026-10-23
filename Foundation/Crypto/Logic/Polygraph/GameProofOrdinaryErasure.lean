import Foundation.Crypto.Logic.Polygraph.GameProofFiniteOrdinary
import Foundation.Logic.SharedInferenceDerivation

/-! Exact rule-tree agreement when an ordinary inference derivation is
interpreted geometrically and exported again. This is a statement about
this common local-rule library, not every possible proof system. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
open Foundation.Logic
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

def treeErasure (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout) :
    Foundation.Logic.Model.Hom (geometric layout relators) (SharedInference.treeModel (theory layout relators)) where
  map _ value := toTree value.1
  preserves := by
    intro rule children
    cases rule with
    | root label => rfl
    | refl p => rfl
    | assoc p q r => rfl
    | leftUnit p => rfl
    | rightUnit p => rfl
    | symm p q support =>
      have same : (children 0).1.needs layout relators = support := (children 0).2
      simp only [geometric, toTree, SharedInference.treeModel, List.ofFn_succ, List.ofFn_zero]
      rw [same]
    | trans p q r first second =>
      have one : (children 0).1.needs layout relators = first := (children 0).2
      have two : (children 1).1.needs layout relators = second := (children 1).2
      simp only [geometric, toTree, SharedInference.treeModel, List.ofFn_succ, List.ofFn_zero]
      rw [one, two]
      rfl
    | seq p p' q q' first second =>
      have one : (children 0).1.needs layout relators = first := (children 0).2
      have two : (children 1).1.needs layout relators = second := (children 1).2
      simp only [geometric, toTree, SharedInference.treeModel, List.ofFn_succ, List.ofFn_zero]
      rw [one, two]
      rfl

theorem ordinary_geometric_tree (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {claim : Claim layout} (derivation : Foundation.Logic.Derivation (theory layout relators)
      (Foundation.Logic.Context.empty (theory layout relators)) claim) :
    toTree (derivation.eval (geometric layout relators) (fun i => Fin.elim0 i)).1 = SharedInference.closedTree derivation := by
  have comparison := Foundation.Logic.Model.eval_hom (treeErasure layout relators) (fun i => Fin.elim0 i) derivation
  exact comparison.trans (SharedInference.closedTree_eval derivation _)

def toDerivation {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout} :
    {a b : Vertex} → {p q : Plan layout a b} → (cell : Cell layout relators p q) →
    Foundation.Logic.Derivation (theory layout relators) (Foundation.Logic.Context.empty (theory layout relators))
      ⟨a, b, p, q, cell.needs layout relators⟩
  | _, _, _, _, .rule label => Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.root label) (fun i => Fin.elim0 i)
  | _, _, _, _, .refl p => Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.refl p) (fun i => Fin.elim0 i)
  | _, _, _, _, @Cell.symm _ _ _ _ _ _ _ _ _ p q child =>
      Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.symm p q (child.needs layout relators)) (fun _ => toDerivation child)
  | _, _, _, _, @Cell.trans _ _ _ _ _ _ _ _ _ p q r first second =>
      Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.trans p q r (first.needs layout relators) (second.needs layout relators))
        (Fin.cases (toDerivation first) (fun _ => toDerivation second))
  | _, _, _, _, @Cell.seq _ _ _ _ _ _ _ _ _ _ p p' q q' first second =>
      Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.seq p p' q q' (first.needs layout relators) (second.needs layout relators))
        (Fin.cases (toDerivation first) (fun _ => toDerivation second))
  | _, _, _, _, .assoc p q r => Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.assoc p q r) (fun i => Fin.elim0 i)
  | _, _, _, _, .leftUnit p => Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.leftUnit p) (fun i => Fin.elim0 i)
  | _, _, _, _, .rightUnit p => Foundation.Logic.Derivation.apply (T := theory layout relators) (Γ := Foundation.Logic.Context.empty (theory layout relators)) (.rightUnit p) (fun i => Fin.elim0 i)

theorem toDerivation_tree {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) :
    SharedInference.closedTree (toDerivation cell) = toTree cell := by
  induction cell with
  | rule => rfl
  | refl => rfl
  | symm child ih => simp only [toDerivation, SharedInference.closedTree, toTree, List.ofFn_succ, List.ofFn_zero, ih]
  | trans first second one two =>
    simp only [toDerivation, SharedInference.closedTree, toTree, List.ofFn_succ, List.ofFn_zero]
    change SharedInference.Tree.node _ [SharedInference.closedTree (toDerivation first), SharedInference.closedTree (toDerivation second)] = _
    rw [one, two]
  | seq first second one two =>
    simp only [toDerivation, SharedInference.closedTree, toTree, List.ofFn_succ, List.ofFn_zero]
    change SharedInference.Tree.node _ [SharedInference.closedTree (toDerivation first), SharedInference.closedTree (toDerivation second)] = _
    rw [one, two]
  | assoc => rfl
  | leftUnit => rfl
  | rightUnit => rfl

theorem toDerivation_compilation [DecidableEq Vertex] [DecidableEq Atom] [DecidableEq Budget] [DecidableEq RelatorId]
    {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {a b : Vertex} {p q : Plan layout a b} (cell : Cell layout relators p q) :
    SharedInference.compile (T := theory layout relators) (SharedInference.closedTree (toDerivation cell)) =
      SharedInference.compile (T := theory layout relators) (toTree cell) :=
  congrArg (SharedInference.compile (T := theory layout relators)) (toDerivation_tree cell)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.CellPresentation
