import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchangeContracts

/-! Full proof-track exchange derived from the existing single-edge exchange.
Both tracks may be empty, composed or formally reversed. -/
namespace CryptoLogic.Polygraph.MixedCircuit.PathExchange
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

def seq {a b c} {p p' : Circuit signature a b} {q q' : Circuit signature b c}
    (left : RewriteTrack (relators := relators) p p') (right : RewriteTrack (relators := relators) q q') :
    Homotopy (.comp ((Placement.seqLeft q).track left) ((Placement.seqRight p').track right))
      (.comp ((Placement.seqRight p).track right) ((Placement.seqLeft q').track left)) :=
  FourNaturality.natural (fun x => Circuit.seq x q) (fun x => Circuit.seq x q')
    (fun change => Step.seqLeft change q) (fun change => Step.seqLeft change q')
    (fun x => (Placement.seqRight x).track right)
    (fun change => (TrackExchange.seqRight change right).symm) left

def tensor {a b c d} {p p' : Circuit signature a b} {q q' : Circuit signature c d}
    (left : RewriteTrack (relators := relators) p p') (right : RewriteTrack (relators := relators) q q') :
    Homotopy (.comp ((Placement.tensorLeft q).track left) ((Placement.tensorRight p').track right))
      (.comp ((Placement.tensorRight p).track right) ((Placement.tensorLeft q').track left)) :=
  FourNaturality.natural (fun x => Circuit.tensor x q) (fun x => Circuit.tensor x q')
    (fun change => Step.tensorLeft change q) (fun change => Step.tensorLeft change q')
    (fun x => (Placement.tensorRight x).track right)
    (fun change => (TrackExchange.tensorRight change right).symm) left

theorem seq_support {a b c} {p p' : Circuit signature a b} {q q' : Circuit signature b c}
    (left : RewriteTrack (relators := relators) p p') (right : RewriteTrack (relators := relators) q q') :
    Homotopy.support (seq left right) = left.support ∪ right.support := by
  unfold seq
  apply TrackExchange.natural_support
  · intro x y path
    change RewriteTrack.support ((Placement.seqLeft q).track path) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) right.boundaries.1
  · intro x y path
    change RewriteTrack.support ((Placement.seqLeft q').track path) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) right.boundaries.2
  · intro x
    rw [Placement.track_support, Placement.needs, Finset.union_comm]
  · intro x y change
    exact (TrackExchange.seqRight_support change right).trans (Finset.union_comm _ _)

theorem tensor_support {a b c d} {p p' : Circuit signature a b} {q q' : Circuit signature c d}
    (left : RewriteTrack (relators := relators) p p') (right : RewriteTrack (relators := relators) q q') :
    Homotopy.support (tensor left right) = left.support ∪ right.support := by
  unfold tensor
  apply TrackExchange.natural_support
  · intro x y path
    change RewriteTrack.support ((Placement.tensorLeft q).track path) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) right.boundaries.1
  · intro x y path
    change RewriteTrack.support ((Placement.tensorLeft q').track path) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) right.boundaries.2
  · intro x
    rw [Placement.track_support, Placement.needs, Finset.union_comm]
  · intro x y change
    exact (TrackExchange.tensorRight_support change right).trans (Finset.union_comm _ _)

end CryptoLogic.Polygraph.MixedCircuit.PathExchange
