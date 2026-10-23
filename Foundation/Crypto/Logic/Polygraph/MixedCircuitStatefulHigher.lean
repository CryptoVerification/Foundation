import Foundation.Crypto.Logic.Polygraph.MixedCircuitStateful
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedHigher

/-! The existing proof tracks and supplied local higher presentations act on
one threaded state. Formal inverse reverses an equality proof, never execution.
Higher-cell repair retains internal guards but endpoint kernel equality already
follows from a single boundary track; no higher-dimensional necessity claim. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule State : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

theorem track_sound {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators condition Value State) {n m} {a b : Circuit signature n m}
    (path : RewriteTrack (relators := relators) a b) (valid : Holds condition (RewriteTrack.support path))
    (left : Holds condition a.needs) (right : Holds condition b.needs) (state : State) (input : Bundle Value n) :
    evaluate model.base a left state input = evaluate model.base b right state input := by
  induction path with
  | refl => rfl
  | step change => exact sound model change valid left right state input
  | comp first second one two =>
      let middle := (valid.restrict Finset.subset_union_left).restrict (RewriteTrack.boundaries first).2
      exact (one (valid.restrict Finset.subset_union_left) left middle).trans
        (two (valid.restrict Finset.subset_union_right) middle right)
  | inv child ih => exact (ih valid right left).symm

theorem track_joint {condition : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (model : CheckedModel relators condition Value State) {n m} {a b : Circuit signature n m}
    (path : RewriteTrack (relators := relators) a b) (valid : Holds condition (RewriteTrack.support path))
    (left : Holds condition a.needs) (right : Holds condition b.needs)
    (law : PMF (Context × (State × Bundle Value n))) :
    law.bind (fun past => (evaluate model.base a left past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate model.base b right past.2.1 past.2.2).map (fun next => (past, next))) := by
  congr 1
  funext past
  rw [track_sound model path valid left right past.2.1 past.2.2]

/-- Both boundary tracks and all internal guards remain available after repair. -/
theorem cell_repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    {basis : HigherBasis relators} (model : CheckedModel relators updated Value State)
    {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) (changed : Finset Requirement)
    (cached : Holds old (PresentedCell.support cell)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (PresentedCell.support cell) changed)) :
    Holds updated (RewriteTrack.support p) ∧ Holds updated (RewriteTrack.support q) ∧
      ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
        ∀ state input, evaluate model.base a left state input = evaluate model.base b right state input := by
  let valid := repair cached unchanged rechecked
  let first := valid.restrict cell.boundaries.1
  let second := valid.restrict cell.boundaries.2
  exact ⟨first, second, first.restrict p.boundaries.1, first.restrict p.boundaries.2,
    fun state input => track_sound model p first _ _ state input⟩

theorem cell_repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    {basis : HigherBasis relators} (model : CheckedModel relators updated Value State)
    {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) (changed : Finset Requirement)
    (cached : Holds old (PresentedCell.support cell)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (PresentedCell.support cell) changed))
    (law : PMF (Context × (State × Bundle Value n))) :
    ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
      law.bind (fun past => (evaluate model.base a left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base b right past.2.1 past.2.2).map (fun next => (past, next))) := by
  obtain ⟨_, _, left, right, equal⟩ := cell_repaired model cell changed cached unchanged rechecked
  refine ⟨left, right, ?_⟩
  congr 1
  funext past
  rw [equal past.2.1 past.2.2]

end CryptoLogic.Polygraph.MixedCircuit.Stateful
