import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigher

/-! Finite dependency accounting for an explicitly supplied higher presentation.
The presentation must cover both boundaries of every generator. Internal
comparison tracks are retained by the recursive accounting. No completeness
or existence of a finite presentation is assumed or concluded. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Logic.Polygraph
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

structure HigherBasis (relators : Rule → Relator signature) where
  Generator : {n m : Port signature} → {a b : Circuit signature n m} →
    RewriteTrack (relators := relators) a b → RewriteTrack (relators := relators) a b → Type
  requirements : {n m : Port signature} → {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → Generator p q → Finset Requirement
  covered : ∀ {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (generator : Generator p q), RewriteTrack.support p ⊆ requirements generator ∧
      RewriteTrack.support q ⊆ requirements generator

abbrev PresentedCell (basis : HigherBasis relators) {n m} {a b : Circuit signature n m}
    (p q : RewriteTrack (relators := relators) a b) := Four basis.Generator p q

namespace PresentedCell
variable {basis : HigherBasis relators}

def support {n m : Port signature} : {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → PresentedCell basis p q → Finset Requirement
  | _, _, _, _, .refl p => RewriteTrack.support p
  | _, _, _, _, .generator generator => basis.requirements generator
  | _, _, _, _, .symm cell => support cell
  | _, _, _, _, .trans first second => support first ∪ support second
  | _, _, _, _, .comp first second => support first ∪ support second
  | _, _, _, _, .inverse child => support child
  | _, _, _, _, .assoc p q r => RewriteTrack.support p ∪ RewriteTrack.support q ∪ RewriteTrack.support r
  | _, _, _, _, .leftUnit p | _, _, _, _, .rightUnit p => RewriteTrack.support p
  | _, _, _, _, .leftInv p | _, _, _, _, .rightInv p => RewriteTrack.support p


theorem boundaries {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) : RewriteTrack.support p ⊆ support cell ∧ RewriteTrack.support q ⊆ support cell := by
  induction cell with
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | generator generator => exact basis.covered generator
  | symm cell ih => exact ⟨ih.2, ih.1⟩
  | trans first second one two =>
      exact ⟨fun _ h => Finset.mem_union_left _ (one.1 h), fun _ h => Finset.mem_union_right _ (two.2 h)⟩
  | comp first second one two => exact ⟨Finset.union_subset_union one.1 two.1, Finset.union_subset_union one.2 two.2⟩
  | inverse child ih => exact ih
  | assoc p q r =>
      simp only [support, RewriteTrack.support, Finset.union_assoc]
      exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | leftUnit p =>
      exact ⟨Finset.union_subset (RewriteTrack.boundaries p).1 (Finset.Subset.refl _), Finset.Subset.refl _⟩
  | rightUnit p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (RewriteTrack.boundaries p).2, Finset.Subset.refl _⟩
  | leftInv p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _), (RewriteTrack.boundaries p).2⟩
  | rightInv p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _), (RewriteTrack.boundaries p).1⟩


/-- Counts only higher syntax constructors. Boundary tracks, circuits,
conditions, and the shared rule library are excluded. -/
def constructorCount {n m : Port signature} : {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → PresentedCell basis p q → Nat
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => 1 + constructorCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second =>
      1 + constructorCount first + constructorCount second
  | _, _, _, _, _ => 1

theorem repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators updated Value) {n m} {a b : Circuit signature n m}
    {p q : RewriteTrack (relators := relators) a b} (cell : PresentedCell basis p q) (changed : Finset Requirement)
    (cached : Holds old (support cell)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (support cell) changed)) :
    Holds updated (RewriteTrack.support p) ∧ Holds updated (RewriteTrack.support q) ∧
      ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
        ∀ input, evaluate model.base a left input = evaluate model.base b right input := by
  let valid := repair cached unchanged rechecked
  let first := valid.restrict cell.boundaries.1
  let second := valid.restrict cell.boundaries.2
  exact ⟨first, second, first.restrict (RewriteTrack.boundaries p).1,
    first.restrict (RewriteTrack.boundaries p).2, fun input => RewriteTrack.sound model p first _ _ input⟩

/-- Preserve arbitrary correlated past data and the original input. This is
kernel equality in the updated model, not equality across model revisions. -/
theorem repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    {Context : Type} (model : CheckedModel relators updated Value) {n m}
    {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) (changed : Finset Requirement)
    (cached : Holds old (support cell)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (support cell) changed))
    (law : PMF (Context × Bundle Value n)) :
    ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
      law.bind (fun past => (evaluate model.base a left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base b right past.2).map (fun next => (past, next))) := by
  obtain ⟨_, _, left, right, equal⟩ := cell.repaired model changed cached unchanged rechecked
  refine ⟨left, right, ?_⟩
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  rw [equal past.2]


end PresentedCell
end CryptoLogic.Polygraph.MixedCircuit
