import Foundation.Crypto.Logic.Polygraph.MixedCircuitCartesianCategoryCritical
import Foundation.Examples.MixedCircuitPresentedWirePass

/-! Retarget the already checked MAC/erasure/sequential-fusion normalization
contract to a presentation that also contains categorical critical diagrams
and transported finite composition coherence. No missing tensor square or
arbitrary cartesian coherence is assumed in the upgrade. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.CategoryWirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
open WirePass
set_option backward.isDefEq.respectTransparency false

abbrev CategoryBasis := CartesianCategoryCritical.basis Structural.Fusion.basis
def presentation : HigherBasis PresentedWirePass.UnionRules :=
  (contextualBasis PresentedWirePass.presentation).sum CategoryBasis
abbrev Cell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def lift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedWirePass.Cell first second) : Cell first second := (cell.injectLeft CategoryBasis).embed

theorem lift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedWirePass.Cell first second) : PresentedCell.support (lift cell) = PresentedCell.support cell := by
  rw [lift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

def categoryLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell CategoryBasis first second) : Cell first second :=
  (cell.injectRight (contextualBasis PresentedWirePass.presentation)).embed

theorem categoryLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell CategoryBasis first second) : PresentedCell.support (categoryLift cell) = PresentedCell.support cell := by
  rw [categoryLift, PresentedCell.embed_support, PresentedCell.injectRight_support]

def contract : PresentedResidual.Contract PresentedWirePass.sourceRules Structural.Fusion.rules presentation where
  exchange := {
    single := fun generator => lift (PresentedWirePass.exchanges.single generator)
    single_support := fun generator => (lift_support _).trans (PresentedWirePass.exchanges.single_support generator) }
  embed := PresentedWirePass.contract.embed
  residual := PresentedWirePass.contract.residual
  square := fun label => lift (PresentedWirePass.contract.square label)
  embed_support := PresentedWirePass.contract.embed_support
  residual_covered := PresentedWirePass.contract.residual_covered
  square_support := fun label => (lift_support _).trans (PresentedWirePass.contract.square_support label)

def comparison {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q) :=
  PresentedResidual.exactTrackSquare contract path

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (PresentedWirePass.framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  exact (PresentedWirePass.framedComparison stage p q).property.symm.trans (PresentedWirePass.framed_support stage p q)

def resolvedPeak {a b} {p q r : Wiring signature a b} (peak : Cartesian.Higher.CategoryCritical.Peak p q r) :=
  categoryLift (CartesianCategoryCritical.resolvedPeak Structural.Fusion.basis peak)

theorem resolvedPeak_support {a b} {p q r : Wiring signature a b} (peak : Cartesian.Higher.CategoryCritical.Peak p q r) :
    PresentedCell.support (resolvedPeak peak) = ∅ := by
  rw [resolvedPeak, categoryLift_support, CartesianCategoryCritical.resolvedPeak_support]

def compositionComparison {E : Port signature → Port signature → Type}
    (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :=
  categoryLift (CartesianCategoryCritical.compositionComparison Structural.Fusion.basis interpret first second)

theorem compositionComparison_support {E : Port signature → Port signature → Type}
    (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    PresentedCell.support (compositionComparison interpret first second) = ∅ := by
  rw [compositionComparison, categoryLift_support, CartesianCategoryCritical.compositionComparison_support]

theorem composition_context_support {E : Port signature → Port signature → Type}
    (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b c d : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q)
    (place : Placement (signature := signature) a b c d) :
    PresentedCell.support ((compositionComparison interpret first second).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, compositionComparison_support, Finset.empty_union]

theorem repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q)
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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.CategoryWirePass
