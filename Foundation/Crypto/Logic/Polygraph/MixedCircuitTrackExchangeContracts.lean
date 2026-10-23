import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchangeSupport

/-! Exact guard support for the four derived mixed track exchanges. -/
namespace CryptoLogic.Polygraph.MixedCircuit.TrackExchange
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem separated_union (first second afterFirst afterSecond : Finset Requirement)
    (one : afterFirst ⊆ first ∪ second) (two : afterSecond ⊆ first ∪ second) :
    (first ∪ afterFirst) ∪ ((first ∪ second) ∪ (second ∪ afterSecond)) = first ∪ second := by
  have left : first ⊆ first ∪ second := Finset.subset_union_left
  have right : second ⊆ first ∪ second := Finset.subset_union_right
  apply Finset.Subset.antisymm
  · repeat' first | assumption | apply Finset.union_subset
  · exact Finset.subset_union_left.trans Finset.subset_union_right

theorem split_union (first second sourceLeft sourceRight : Finset Requirement)
    (one : sourceLeft ⊆ first) (two : sourceRight ⊆ second) :
    (first ∪ sourceRight) ∪ (sourceLeft ∪ second) = first ∪ second := by
  have left : first ⊆ first ∪ second := Finset.subset_union_left
  have right : second ⊆ first ∪ second := Finset.subset_union_right
  have one' := one.trans left
  have two' := two.trans right
  apply Finset.Subset.antisymm
  · repeat' first | assumption | apply Finset.union_subset
  · intro label member
    rcases Finset.mem_union.mp member with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

theorem separated_support {a b} {p q r : Circuit signature a b}
    {first : Step relators p q} {second : Step relators p r} (apart : Separated first second) :
    Homotopy.support (separated apart) = first.support ∪ second.support := by
  simp only [separated, Homotopy.support, Exchange.support, RewriteTrack.support]
  exact separated_union first.support second.support apart.diamond.afterFirst.support apart.diamond.afterSecond.support
    apart.no_new_conditions.1 apart.no_new_conditions.2

theorem seqSplit_support {a b c} {p p' : Circuit signature a b} {q q' : Circuit signature b c}
    (left : Step relators p p') (right : Step relators q q') :
    Homotopy.support (separated (.seqLR left right)) = left.support ∪ right.support := by
  rw [separated_support]
  simp only [Step.support]
  exact split_union left.support right.support p.needs q.needs left.boundaries.1 right.boundaries.1

theorem tensorSplit_support {a b c d} {p p' : Circuit signature a b} {q q' : Circuit signature c d}
    (left : Step relators p p') (right : Step relators q q') :
    Homotopy.support (separated (.tensorLR left right)) = left.support ∪ right.support := by
  rw [separated_support]
  simp only [Step.support]
  exact split_union left.support right.support p.needs q.needs left.boundaries.1 right.boundaries.1

theorem seqRight_support {a b c} {p p' : Circuit signature a b} (change : Step relators p p')
    {q q' : Circuit signature b c} (path : RewriteTrack (relators := relators) q q') :
    Homotopy.support (seqRight change path) = path.support ∪ change.support := by
  unfold seqRight
  apply natural_support
  · intro x y track
    change RewriteTrack.support ((Placement.seqRight p).track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.1
  · intro x y track
    change RewriteTrack.support ((Placement.seqRight p').track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.2
  · intro x
    exact Finset.union_comm _ _
  · intro x y edge
    change Homotopy.support (separated (Separated.seqLR change edge)) = _
    rw [seqSplit_support, Finset.union_comm]

theorem seqLeft_support {a b c} {q q' : Circuit signature b c} (change : Step relators q q')
    {p p' : Circuit signature a b} (path : RewriteTrack (relators := relators) p p') :
    Homotopy.support (seqLeft change path) = path.support ∪ change.support := by
  unfold seqLeft
  apply natural_support
  · intro x y track
    change RewriteTrack.support ((Placement.seqLeft q).track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.1
  · intro x y track
    change RewriteTrack.support ((Placement.seqLeft q').track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.2
  · intro x
    rfl
  · intro x y edge
    exact seqSplit_support edge change

theorem tensorRight_support {a b c d} {p p' : Circuit signature a b} (change : Step relators p p')
    {q q' : Circuit signature c d} (path : RewriteTrack (relators := relators) q q') :
    Homotopy.support (tensorRight change path) = path.support ∪ change.support := by
  unfold tensorRight
  apply natural_support
  · intro x y track
    change RewriteTrack.support ((Placement.tensorRight p).track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.1
  · intro x y track
    change RewriteTrack.support ((Placement.tensorRight p').track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.2
  · intro x
    exact Finset.union_comm _ _
  · intro x y edge
    change Homotopy.support (separated (Separated.tensorLR change edge)) = _
    rw [tensorSplit_support, Finset.union_comm]

theorem tensorLeft_support {a b c d} {q q' : Circuit signature c d} (change : Step relators q q')
    {p p' : Circuit signature a b} (path : RewriteTrack (relators := relators) p p') :
    Homotopy.support (tensorLeft change path) = path.support ∪ change.support := by
  unfold tensorLeft
  apply natural_support
  · intro x y track
    change RewriteTrack.support ((Placement.tensorLeft q).track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.1
  · intro x y track
    change RewriteTrack.support ((Placement.tensorLeft q').track track) ⊆ _
    rw [Placement.track_support]
    exact Finset.union_subset_union (Finset.Subset.refl _) change.boundaries.2
  · intro x
    rfl
  · intro x y edge
    exact tensorSplit_support edge change

end CryptoLogic.Polygraph.MixedCircuit.TrackExchange
