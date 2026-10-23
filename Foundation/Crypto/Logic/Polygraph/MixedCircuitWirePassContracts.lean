import Foundation.Crypto.Logic.Polygraph.MixedCircuitWirePassNaturality
import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchangeContracts

/-! Exact guard contracts for generated contextual wire-pass squares. The
root footprint is checked separately, rather than inferred from endpoints. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem normalizedTrack_support (contract : RootCompatibility original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := original) p q) :
    RewriteTrack.support (normalizedTrack contract path) = RewriteTrack.support path := by
  induction path <;> simp_all only [normalizedTrack, Track.map, RewriteTrack.support, residual_support, output_needs]

theorem embeddedMap_support {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := original) p q) :
    RewriteTrack.support (path.map id (fun change => embedStep (original := original) change)) = RewriteTrack.support path := by
  induction path <;> simp_all only [Track.map, RewriteTrack.support, embedStep_support, id_eq]

theorem square_support (contract : RootCompatibility original)
    (rootSupport : ∀ label, Homotopy.support (contract.square label) = (Primitive.rule (relators := original) label).support)
    {a b} {p q : Circuit signature a b} (change : Step original p q) :
    Homotopy.support (square contract change) = change.support := by
  apply Finset.Subset.antisymm
  · induction change with
    | root primitive => cases primitive; exact (rootSupport _).le
    | seqLeft child fixed ih | tensorLeft child fixed ih =>
        have hg : child.support ⊆ child.support ∪ fixed.needs := Finset.subset_union_left
        have hf : fixed.needs ⊆ child.support ∪ fixed.needs := Finset.subset_union_right
        have hp := child.boundaries.1.trans hg
        have hq := child.boundaries.2.trans hg
        have hc := ih.trans hg
        simp only [square, Homotopy.support, Homotopy.whisker_support, Placement.track_support,
          Placement.map_support, RewriteTrack.support]
        first | rw [TrackExchange.seqRight_support] | rw [TrackExchange.tensorRight_support]
        simp only [Placement.needs, witness_support, residual_support, embedStep_support, output_needs, Step.support]
        clear rootSupport ih
        repeat' first | assumption | apply Finset.union_subset
    | seqRight fixed child ih | tensorRight fixed child ih =>
        have hg : child.support ⊆ fixed.needs ∪ child.support := Finset.subset_union_right
        have hf : fixed.needs ⊆ fixed.needs ∪ child.support := Finset.subset_union_left
        have hp := child.boundaries.1.trans hg
        have hq := child.boundaries.2.trans hg
        have hc := ih.trans hg
        simp only [square, Homotopy.support, Homotopy.whisker_support, Placement.track_support,
          Placement.map_support, RewriteTrack.support]
        first | rw [TrackExchange.seqLeft_support] | rw [TrackExchange.tensorLeft_support]
        simp only [Placement.needs, witness_support, residual_support, embedStep_support, output_needs, Step.support]
        clear rootSupport ih
        repeat' first | assumption | apply Finset.union_subset
  · intro label member
    apply (Homotopy.boundaries (square contract change)).1
    change label ∈ (embedStep (original := original) change).support ∪ (witness (original := original) q).support
    exact Finset.mem_union_left _ (by rw [embedStep_support]; exact member)

/-- Generate the whole-track comparison and its footprint in one dependent
result, including tracks that use inverse equalities. -/
def exactTrackSquare (contract : RootCompatibility original)
    (rootSupport : ∀ label, Homotopy.support (contract.square label) = (Primitive.rule (relators := original) label).support)
    {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := original) p q) :
    { cell : Homotopy (.comp (embedTrack (original := original) path) (witness (original := original) q)) (.comp (witness (original := original) p) (normalizedTrack contract path)) //
      Homotopy.support cell = RewriteTrack.support path } := by
  have mapped : path.map id (fun change => embedStep (original := original) change) = embedTrack (original := original) path := by
    induction path <;> simp_all only [Track.map, embedTrack, id_eq]
  let raw : Homotopy
      (.comp (path.map id (fun change => embedStep (original := original) change)) (witness (original := original) q))
      (.comp (witness (original := original) p) (normalizedTrack contract path)) :=
    FourNaturality.natural id output (fun change => embedStep (original := original) change)
      (fun change => residual contract change) (witness (original := original)) (fun change => square contract change) path
  have accounted : Homotopy.support raw = RewriteTrack.support path := by
    change Homotopy.support (FourNaturality.natural id output (fun change => embedStep (original := original) change)
      (fun change => residual contract change) (witness (original := original)) (fun change => square contract change) path) = _
    have result := TrackExchange.natural_support (relators := rules original) (sourceRules := original) id output (fun change => embedStep (original := original) change)
      (fun change => residual contract change) (witness (original := original)) (fun change => square contract change) ∅
      (fun track => by
        change RewriteTrack.support (track.map id (fun change => embedStep (original := original) change)) ⊆ _
        exact (embeddedMap_support track).le.trans Finset.subset_union_left)
      (fun track => by
        change RewriteTrack.support (normalizedTrack contract track) ⊆ _
        exact (normalizedTrack_support contract track).le.trans Finset.subset_union_left)
      (fun circuit => by
        change RewriteTrack.support (witness (original := original) circuit) = _
        exact (witness_support circuit).trans (Finset.union_empty _).symm)
      (fun change => (square_support contract rootSupport change).trans (Finset.union_empty _).symm) path
    exact result.trans (Finset.union_empty _)
  have result : { cell : Homotopy
      (.comp (path.map id (fun change => embedStep (original := original) change)) (witness (original := original) q))
      (.comp (witness (original := original) p) (normalizedTrack contract path)) //
      Homotopy.support cell = RewriteTrack.support path } := ⟨raw, accounted⟩
  let family (edge : RewriteTrack (relators := rules original) p q) :=
    { cell : Homotopy (.comp edge (witness (original := original) q))
        (.comp (witness (original := original) p) (normalizedTrack contract path)) //
      Homotopy.support cell = RewriteTrack.support path }
  exact cast (congrArg family mapped) result

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
