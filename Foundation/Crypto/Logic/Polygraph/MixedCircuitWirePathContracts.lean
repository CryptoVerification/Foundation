import Foundation.Crypto.Logic.Polygraph.MixedCircuitWirePathCompatibility
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPathNaturalitySupport

/-! Guard-preserving higher compatibility with empty and multi-step residuals.
Residual support may shrink; the generated comparison still retains exactly
all source-track requirements, including when a rule is erased. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass.PathResidual
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule SourceRule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
variable {sourceRules : SourceRule → Relator signature}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem embeddedTrack_support (contract : Contract sourceRules original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) : (embeddedTrack contract path).support = path.support := by
  induction path <;> simp_all only [embeddedTrack, FourPathNaturality.replace, RewriteTrack.support, embedStep_support, id_eq]

theorem residualTrack_covered (contract : Contract sourceRules original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) : (residualTrack contract path).support ⊆ path.support := by
  induction path with
  | refl => simp only [residualTrack, FourPathNaturality.replace, RewriteTrack.support, output_needs]; exact Finset.Subset.refl _
  | step change => exact residualStep_covered contract change
  | comp first second one two => exact Finset.union_subset_union one two
  | inv child ih => exact ih

theorem square_support (contract : Contract sourceRules original) {a b} {p q : Circuit signature a b}
    (change : Step sourceRules p q) : Homotopy.support (square contract change) = change.support := by
  apply Finset.Subset.antisymm
  · induction change with
    | root primitive => cases primitive; exact (contract.square_support _).le
    | seqLeft child fixed ih | tensorLeft child fixed ih =>
        have hg : child.support ⊆ child.support ∪ fixed.needs := Finset.subset_union_left
        have hf : fixed.needs ⊆ child.support ∪ fixed.needs := Finset.subset_union_right
        have hp := child.boundaries.1.trans hg
        have hq := child.boundaries.2.trans hg
        have hc := ih.trans hg
        have hr := (residualStep_covered contract child).trans hg
        simp only [square, Homotopy.support, Homotopy.whisker_support, Placement.track_support,
          Placement.map_support, RewriteTrack.support]
        first | rw [PathExchange.seq_support] | rw [PathExchange.tensor_support]
        simp only [Placement.needs, witness_support, embedStep_support, output_needs, Step.support]
        clear ih
        repeat' first | assumption | apply Finset.union_subset
    | seqRight fixed child ih | tensorRight fixed child ih =>
        have hg : child.support ⊆ fixed.needs ∪ child.support := Finset.subset_union_right
        have hf : fixed.needs ⊆ fixed.needs ∪ child.support := Finset.subset_union_left
        have hp := child.boundaries.1.trans hg
        have hq := child.boundaries.2.trans hg
        have hc := ih.trans hg
        have hr := (residualStep_covered contract child).trans hg
        simp only [square, Homotopy.support, Homotopy.whisker_support, Placement.track_support,
          Placement.map_support, RewriteTrack.support]
        first | rw [TrackExchange.seqLeft_support] | rw [TrackExchange.tensorLeft_support]
        simp only [Placement.needs, witness_support, embedStep_support, output_needs, Step.support]
        clear ih
        repeat' first | assumption | apply Finset.union_subset
  · intro label member
    apply (Homotopy.boundaries (square contract change)).1
    change label ∈ (embedStep contract change).support ∪ (witness (original := original) q).support
    exact Finset.mem_union_left _ (by rw [embedStep_support]; exact member)

def exactTrackSquare (contract : Contract sourceRules original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) :
    { cell : Homotopy (.comp (embeddedTrack contract path) (witness (original := original) q))
        (.comp (witness (original := original) p) (residualTrack contract path)) // cell.support = path.support } := by
  refine ⟨trackSquare contract path, ?_⟩
  change Homotopy.support (FourPathNaturality.natural id output (fun change => .step (embedStep contract change))
    (fun change => residualStep contract change) (witness (original := original)) (fun change => square contract change) path) = _
  have result := PathNaturality.natural_support (relators := rules original) (sourceRules := sourceRules)
    id output (fun change => .step (embedStep contract change)) (fun change => residualStep contract change)
    (witness (original := original)) (fun change => square contract change) ∅
    (fun track => by
      change (embeddedTrack contract track).support ⊆ _
      exact (embeddedTrack_support contract track).le.trans Finset.subset_union_left)
    (fun track => by
      change (residualTrack contract track).support ⊆ _
      exact (residualTrack_covered contract track).trans Finset.subset_union_left)
    (fun circuit => (witness_support (original := original) circuit).trans (Finset.union_empty _).symm)
    (fun change => (square_support contract change).trans (Finset.union_empty _).symm) path
  exact result.trans (Finset.union_empty _)

/-- Repair uses source-track guards even when residual rewrites disappear.
The equality is within the updated checked stateful model. -/
theorem repaired_joint {State Context : Type} {old updated : Requirement → Prop}
    {Value : signature.PortAtom → Type} (model : CheckedModel original updated Value State)
    (contract : Contract sourceRules original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) (changed : Finset Requirement)
    (cached : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds old path.support)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated
      (CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.fresh path.support changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated p.needs,
    ∃ right : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated (output q).needs,
      law.bind (fun past => (evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base (output q) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let comparison := exactTrackSquare contract path
  have valid : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated (Homotopy.support comparison.val) := by
    rw [comparison.property]
    exact CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.repair cached unchanged rechecked
  let route : RewriteTrack (relators := rules original) p (output q) :=
    .comp (embeddedTrack contract path) (witness (original := original) q)
  let guard := valid.restrict (Homotopy.boundaries comparison.val).1
  refine ⟨guard.restrict route.boundaries.1, guard.restrict route.boundaries.2, ?_⟩
  exact track_joint (checked model) route guard _ _ law

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass.PathResidual
