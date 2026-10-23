import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedWireContracts
import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigherBasisSum
import Foundation.Crypto.Logic.Polygraph.MixedCircuitCartesianUnitCritical
import Foundation.Examples.MixedCircuitSequentialFusionWirePass
import Foundation.Examples.MixedCircuitErasedWirePath

/-! One actual catalogue mixes MAC contraction, erased unit wiring, and
canonical sequential fusion. Its generated comparisons use a presentation
containing both the existing fusion squares and the explicit unit critical
extension. Tensor-fusion compatibility and completeness remain open. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.PresentedWirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
open WirePass
set_option backward.isDefEq.respectTransparency false

abbrev UnionRules := StatefulWiring.UnionRules
abbrev UnitBasis := CartesianUnitCritical.basis Structural.Fusion.basis
def presentation : HigherBasis UnionRules := StatefulWiring.basis.sum UnitBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def fusionLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.Cell first second) : Cell first second := (cell.injectLeft UnitBasis).embed

theorem fusionLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.Cell first second) : PresentedCell.support (fusionLift cell) = PresentedCell.support cell := by
  rw [fusionLift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

def unitComparison (a : Port signature) :=
  ((CartesianUnitCritical.unitCell Structural.Fusion.basis a).injectRight StatefulWiring.basis).embed

theorem unitComparison_support (a : Port signature) : PresentedCell.support (unitComparison a) = ∅ := by
  rw [unitComparison, PresentedCell.embed_support, PresentedCell.injectRight_support,
    CartesianUnitCritical.unitCell_support]

def exchanges : PresentedExchange.Data presentation where
  single generator := fusionLift (.generator (.root (.existing (.root (.separated generator)))))
  single_support generator := by rw [fusionLift_support]; rfl

inductive Root where
  | crypto (stage : Nat)
  | erase
  | fusion {a b c : Port signature} (p : Wiring signature a b) (q : Wiring signature b c)

def sourceRules : Root → Relator signature
  | .crypto stage => MAC.relators stage
  | .erase => ErasedWirePath.sourceRules ()
  | .fusion p q => Structural.Fusion.rules (.existing (.fuseSeq p q))

def cryptoStep (stage : Nat) : Step UnionRules (MAC.before stage) (MAC.after stage) :=
  Stateful.WiringUnion.embedStep (.root (.rule (relators := Structural.Fusion.rules)
    (Structural.Fusion.Rule.existing (Structural.Rule.crypto stage))))

def rootEmbed : (label : Root) → Step UnionRules (sourceRules label).left (sourceRules label).right
  | .crypto stage => cryptoStep stage
  | .erase => wireStep (Cartesian.Step.root Cartesian.Root.unitIdentity)
  | .fusion p q => StatefulWiring.seqFusion p q

def rootResidual : (label : Root) → RewriteTrack (relators := UnionRules)
    (output (sourceRules label).left) (output (sourceRules label).right)
  | .crypto stage => .step (cryptoStep stage)
  | .erase => .refl (Circuit.wire (signature := signature) (Wire.discard .unit))
  | .fusion p q => StatefulWiring.WireFusionResidual.seqResidual p q

def rootSquare : (label : Root) →
    Cell (.comp (.step (rootEmbed label)) (witness (original := Structural.Fusion.rules) (sourceRules label).right))
      (.comp (witness (original := Structural.Fusion.rules) (sourceRules label).left) (rootResidual label))
  | .crypto stage =>
      (Four.rightUnit (.step (cryptoStep stage))).trans
        ((Four.leftUnit (.step (cryptoStep stage))).symm.trans
          (Four.comp (Four.leftUnit (.refl (MAC.before stage))).symm (.refl (.step (cryptoStep stage)))))
  | .erase => .refl _
  | .fusion p q => fusionLift (StatefulWiring.SequentialFusionWirePass.square p q).val

theorem rootSquare_support (label : Root) :
    PresentedCell.support (rootSquare label) = (Primitive.rule (relators := sourceRules) label).support := by
  cases label with
  | crypto stage =>
      change PresentedCell.support (rootSquare (.crypto stage)) = (cryptoStep stage).support
      simp only [rootSquare, PresentedCell.support, RewriteTrack.support]
      ext label
      have covered : label ∈ (MAC.before stage).needs → label ∈ (cryptoStep stage).support :=
        fun member => (cryptoStep stage).boundaries.1 member
      simp only [Finset.mem_union] at *
      tauto
  | erase => rfl
  | fusion p q =>
      exact (fusionLift_support _).trans (StatefulWiring.SequentialFusionWirePass.square p q).property

def contract : PresentedResidual.Contract sourceRules Structural.Fusion.rules presentation where
  exchange := exchanges
  embed := rootEmbed
  residual := rootResidual
  square := rootSquare
  embed_support label := by cases label <;> rfl
  residual_covered label := by
    cases label with
    | crypto stage => exact Finset.Subset.refl _
    | erase => exact Finset.Subset.refl _
    | fusion p q => rw [rootResidual, StatefulWiring.WireFusionResidual.seqResidual_support]; exact Finset.empty_subset _
  square_support := rootSquare_support

def comparison {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := sourceRules) p q) :=
  PresentedResidual.exactTrackSquare contract path

def mixedPath (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    RewriteTrack (relators := sourceRules)
      (.tensor (.seq (.wire p) (.wire q)) (.tensor (MAC.before stage) (.wire (.identity .unit))))
      (.tensor (.wire (Wire.seq p q)) (.tensor (MAC.after stage) (.wire (.discard .unit)))) :=
  .comp (.step (.tensorLeft (.root (Primitive.rule (relators := sourceRules) (Root.fusion p q)))
      (.tensor (MAC.before stage) (.wire (.identity .unit)))))
    (.comp (.step (.tensorRight (.wire (Wire.seq p q))
      (.tensorLeft (.root (Primitive.rule (relators := sourceRules) (Root.crypto stage))) (.wire (.identity .unit)))))
      (.step (.tensorRight (.wire (Wire.seq p q))
        (.tensorRight (MAC.after stage) (.root (Primitive.rule (relators := sourceRules) Root.erase))))))

theorem mixed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (comparison (mixedPath stage p q)).val = {stage, stage + 1} := by
  rw [(comparison (mixedPath stage p q)).property]
  simp [mixedPath, RewriteTrack.support, Step.support, Primitive.support, Relator.support,
    sourceRules, Structural.Fusion.rules, Structural.rules, ErasedWirePath.sourceRules,
    Circuit.needs, MAC.relators, MAC.before, MAC.after, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout]

def fullCopyDiscard (c : Port signature) :
    Wiring signature (.pair c (.pair MAC.finish .unit)) (.pair c (.pair MAC.finish .unit)) :=
  .seq (.seq (.copy _) (.tensor (.identity _) (.discard _))) (.rightUnit _)

def framedPath (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  (Placement.seqLeft (Circuit.wire (fullCopyDiscard c))).track (mixedPath stage p q)

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  have sourceSupport : RewriteTrack.support (mixedPath stage p q) = {stage, stage + 1} :=
    (comparison (mixedPath stage p q)).property.symm.trans (mixed_support stage p q)
  simp only [framedPath, Placement.track_support, sourceSupport, Placement.needs,
    Circuit.needs, Finset.union_empty]

theorem unitComparison_context_support {a x y : Port signature}
    (place : Placement (signature := signature) a a x y) :
    PresentedCell.support ((unitComparison a).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, unitComparison_support, Finset.empty_union]

/-- This applies to any source-catalogue path, including framedPath. The
model is the original checked MAC model extended by actual structural rules;
no new native execution or advantage bound is asserted. -/
theorem repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := sourceRules) p q)
    (changed : Finset Nat)
    (cached : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds old path.support)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated
      (CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.fresh path.support changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated p.needs,
    ∃ right : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds updated (output q).needs,
      law.bind (fun past => (Stateful.evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (output q) right past.2.1 past.2.2).map (fun next => (past, next))) :=
  PresentedResidual.repaired_joint (StatefulStructural.allRules model) contract path
    changed cached unchanged rechecked law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.PresentedWirePass
