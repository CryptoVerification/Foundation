import Foundation.Crypto.Logic.Polygraph.MixedCircuitWireNormalization
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedExchange
import Foundation.Logic.Polygraph.FourPathNaturality

/-! Path-valued compatibility in a supplied contextual higher presentation.
Root comparisons may use actual critical diagrams beyond separated exchange.
Only local roots and single exchanges are supplied; contextual and whole-track
comparisons are generated, including erased/multi-step residuals. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass.PresentedResidual
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule SourceRule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
variable {sourceRules : SourceRule → Relator signature}
variable {presentation : HigherBasis (rules original)}
set_option backward.isDefEq.respectTransparency false

structure Contract (sourceRules : SourceRule → Relator signature) (original : Rule → Relator signature)
    (presentation : HigherBasis (rules original)) where
  exchange : PresentedExchange.Data presentation
  embed : (label : SourceRule) → Step (rules original) (sourceRules label).left (sourceRules label).right
  residual : (label : SourceRule) → RewriteTrack (relators := rules original)
    (output (sourceRules label).left) (output (sourceRules label).right)
  square : (label : SourceRule) →
    PresentedCell (contextualBasis presentation) (.comp (.step (embed label)) (witness (sourceRules label).right))
      (.comp (witness (sourceRules label).left) (residual label))
  embed_support : ∀ label, (embed label).support = (Primitive.rule (relators := sourceRules) label).support
  residual_covered : ∀ label, (residual label).support ⊆ (Primitive.rule (relators := sourceRules) label).support
  square_support : ∀ label, PresentedCell.support (square label) = (Primitive.rule (relators := sourceRules) label).support

def embedStep (contract : Contract sourceRules original presentation) : {a b : Port signature} →
    {p q : Circuit signature a b} → Step sourceRules p q → Step (rules original) p q
  | _, _, _, _, .root (.rule label) => contract.embed label
  | _, _, _, _, .seqLeft child fixed => .seqLeft (embedStep contract child) fixed
  | _, _, _, _, .seqRight fixed child => .seqRight fixed (embedStep contract child)
  | _, _, _, _, .tensorLeft child fixed => .tensorLeft (embedStep contract child) fixed
  | _, _, _, _, .tensorRight fixed child => .tensorRight fixed (embedStep contract child)

def residualStep (contract : Contract sourceRules original presentation) : {a b : Port signature} →
    {p q : Circuit signature a b} → Step sourceRules p q → RewriteTrack (relators := rules original) (output p) (output q)
  | _, _, _, _, .root (.rule label) => contract.residual label
  | _, _, _, _, .seqLeft child fixed => (Placement.seqLeft (output fixed)).track (residualStep contract child)
  | _, _, _, _, .seqRight fixed child => (Placement.seqRight (output fixed)).track (residualStep contract child)
  | _, _, _, _, .tensorLeft child fixed => (Placement.tensorLeft (output fixed)).track (residualStep contract child)
  | _, _, _, _, .tensorRight fixed child => (Placement.tensorRight (output fixed)).track (residualStep contract child)

theorem embedStep_support (contract : Contract sourceRules original presentation) {a b} {p q : Circuit signature a b}
    (change : Step sourceRules p q) : (embedStep contract change).support = change.support := by
  induction change with
  | root primitive => cases primitive; exact contract.embed_support _
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [embedStep, Step.support, ih]

theorem residualStep_covered (contract : Contract sourceRules original presentation) {a b} {p q : Circuit signature a b}
    (change : Step sourceRules p q) : (residualStep contract change).support ⊆ change.support := by
  induction change with
  | root primitive => cases primitive; exact contract.residual_covered _
  | seqLeft child fixed ih | tensorLeft child fixed ih =>
      simpa only [residualStep, Placement.track_support, Placement.needs, output_needs, Step.support] using
        Finset.union_subset_union ih (Finset.Subset.refl fixed.needs)
  | seqRight fixed child ih | tensorRight fixed child ih =>
      simpa only [residualStep, Placement.track_support, Placement.needs, output_needs, Step.support, Finset.union_comm] using
        Finset.union_subset_union ih (Finset.Subset.refl fixed.needs)

def square (contract : Contract sourceRules original presentation) : {a b : Port signature} → {p q : Circuit signature a b} →
    (change : Step sourceRules p q) →
    PresentedCell (contextualBasis presentation) (.comp (.step (embedStep contract change)) (witness q))
      (.comp (witness p) (residualStep contract change))
  | _, _, _, _, .root (.rule label) => contract.square label
  | _, _, _, _, .seqLeft (a := p) (a' := p') child fixed =>
      (Four.assoc (.step (.seqLeft (embedStep contract child) fixed))
        ((Placement.seqLeft fixed).track (witness p'))
        ((Placement.seqRight (output p')).track (witness fixed))).symm.trans
      ((Four.comp ((square contract child).whisker (.seqLeft fixed)) (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) (contract.exchange.lift (PathExchange.seq (residualStep contract child) (witness fixed)))).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .seqRight fixed child =>
      (Four.assoc _ _ _).symm.trans
      ((Four.comp (contract.exchange.lift (TrackExchange.seqLeft (embedStep contract child) (witness fixed))).symm (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) ((square contract child).whisker (.seqRight (output fixed)))).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .tensorLeft (a := p) (a' := p') child fixed =>
      (Four.assoc (.step (.tensorLeft (embedStep contract child) fixed))
        ((Placement.tensorLeft fixed).track (witness p'))
        ((Placement.tensorRight (output p')).track (witness fixed))).symm.trans
      ((Four.comp ((square contract child).whisker (.tensorLeft fixed)) (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) (contract.exchange.lift (PathExchange.tensor (residualStep contract child) (witness fixed)))).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .tensorRight fixed child =>
      (Four.assoc _ _ _).symm.trans
      ((Four.comp (contract.exchange.lift (TrackExchange.tensorLeft (embedStep contract child) (witness fixed))).symm (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) ((square contract child).whisker (.tensorRight (output fixed)))).trans
        (Four.assoc _ _ _).symm)))

def embeddedTrack (contract : Contract sourceRules original presentation) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) : RewriteTrack (relators := rules original) p q :=
  FourPathNaturality.replace id (fun change => .step (embedStep contract change)) path

def residualTrack (contract : Contract sourceRules original presentation) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) : RewriteTrack (relators := rules original) (output p) (output q) :=
  FourPathNaturality.replace output (fun change => residualStep contract change) path

def trackSquare (contract : Contract sourceRules original presentation) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := sourceRules) p q) :
    PresentedCell (contextualBasis presentation) (.comp (embeddedTrack contract path) (witness q)) (.comp (witness p) (residualTrack contract path)) :=
  FourPathNaturality.natural id output (fun change => .step (embedStep contract change))
    (fun change => residualStep contract change) (witness (original := original)) (fun change => square contract change) path

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass.PresentedResidual
