import Foundation.Examples.MixedCircuitRootWireDefinitions
import Foundation.Examples.MixedCircuitOldWireElimination

/-! Whole mixed-track elimination in the root-only definition basis. The
old expansion algorithms are reused as first-level syntax transformations;
the old contextual-definition higher basis/eliminators are not used. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.RootDefinitions
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

structure ExactCell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := UnionRules) p q) (footprint : Finset Nat) where
  cell : Cell first second
  support_eq : PresentedCell.support cell = footprint

def eliminatePrimitive {a b} {p q : Circuit signature a b} (change : Primitive UnionRules p q) :
    ExactCell (.step (.root change)) (OldDefinitions.expandPrimitive change) change.support := by
  cases rootView change with
  | oldWire change =>
      refine ⟨eliminateWireStep change, ?_⟩
      change PresentedCell.support (eliminateWireStep change) = (oldEdit change).support
      rw [eliminateWireStep_support, OldDefinitions.oldEdit_support]
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => exact ⟨.refl _, rfl⟩

def eliminateStep : {a b : Port signature} → {p q : Circuit signature a b} → (change : Step UnionRules p q) →
    ExactCell (.step change) (OldDefinitions.expandStep change) change.support
  | _, _, _, _, .root primitive => eliminatePrimitive primitive
  | _, _, _, _, .seqLeft change fixed => by
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.seqLeft fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support]
  | _, _, _, _, .seqRight fixed change => by
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.seqRight fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support, Finset.union_comm]
  | _, _, _, _, .tensorLeft change fixed => by
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.tensorLeft fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support]
  | _, _, _, _, .tensorRight fixed change => by
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.tensorRight fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support, Finset.union_comm]

def eliminateTrack {a b : Port signature} : {p q : Circuit signature a b} → (path : RewriteTrack (relators := UnionRules) p q) →
    ExactCell path (OldDefinitions.expandTrack path) (RewriteTrack.support path)
  | _, _, .refl p => ⟨.refl _, rfl⟩
  | _, _, .step change => eliminateStep change
  | _, _, .comp first second =>
      let one := eliminateTrack first
      let two := eliminateTrack second
      ⟨.comp one.cell two.cell, by simp only [PresentedCell.support, one.support_eq, two.support_eq, RewriteTrack.support]⟩
  | _, _, .inv child =>
      let proof := eliminateTrack child
      ⟨.inverse proof.cell, by simp only [PresentedCell.support, proof.support_eq, RewriteTrack.support]⟩

theorem eliminatePrimitive_definitions {a b} {p q : Circuit signature a b} (change : Primitive UnionRules p q) :
    definitions (eliminatePrimitive change).cell = OldDefinitions.legacyPrimitive change := by
  cases rootView change with
  | oldWire change => exact eliminateWireStep_definitions change
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => rfl

theorem eliminateStep_definitions {a b} {p q : Circuit signature a b} (change : Step UnionRules p q) :
    definitions (eliminateStep change).cell = OldDefinitions.legacyStep change := by
  induction change with
  | root primitive => exact eliminatePrimitive_definitions primitive
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simpa only [eliminateStep, definitions_whisker, OldDefinitions.legacyStep] using ih

theorem eliminateTrack_definitions {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    definitions (eliminateTrack path).cell = OldDefinitions.legacyTrack path := by
  induction path with
  | refl => rfl
  | step change => exact eliminateStep_definitions change
  | comp first second one two => simp only [eliminateTrack, definitions, OldDefinitions.legacyTrack, one, two]
  | inv child ih => exact ih

/-- Existing comparisons are transferred compositionally to expanded boundary
tracks. Their internal prior-library generators need not disappear. -/
def expandComparison {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    Cell (OldDefinitions.expandTrack first) (OldDefinitions.expandTrack second) :=
  (eliminateTrack first).cell.symm.trans ((embedPrior cell).trans (eliminateTrack second).cell)

theorem expandComparison_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    PresentedCell.support (expandComparison cell) = PresentedCell.support cell := by
  simp only [expandComparison, PresentedCell.support, embedPrior_support,
    (eliminateTrack first).support_eq, (eliminateTrack second).support_eq]
  rw [Finset.union_eq_left.mpr cell.boundaries.2, Finset.union_eq_right.mpr cell.boundaries.1]

theorem expandComparison_definitions {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    definitions (expandComparison cell) = OldDefinitions.legacyTrack first + OldDefinitions.legacyTrack second := by
  simp only [expandComparison, definitions, eliminateTrack_definitions, embedPrior_definitions, Nat.zero_add]

theorem elimination_repaired_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := UnionRules) p q) (changed : Finset Nat)
    (cached : Holds old (RewriteTrack.support path)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (RewriteTrack.support path) changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : Holds updated p.needs, ∃ right : Holds updated q.needs,
      law.bind (fun past => (Stateful.evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base q right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := eliminateTrack path
  have cached' : Holds old (PresentedCell.support proof.cell) := by rw [proof.support_eq]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof.cell) changed) := by rw [proof.support_eq]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof.cell changed cached' unchanged rechecked' law

/-- info: (1, 0, 20, 0, 2793) -/
#guard_msgs in
#eval Id.run do
  let i : Wiring signature finish finish := .identity finish
  let root := Rewrite.Step.root (Rewrite.Root.interchange i i i i)
  let one := Rewrite.Step.seqLeft root (Wire.identity (.pair finish finish))
  let two := Rewrite.Step.seqRight (Wire.identity (.pair finish finish)) one
  let three := Rewrite.Step.tensorLeft two (Wire.identity finish)
  let four := Rewrite.Step.tensorRight (Wire.identity finish) three
  let path := Track.step (StatefulWiring.Overlap.oldEdit four)
  let proof := eliminateTrack path
  return (definitions proof.cell, OldDefinitions.legacyTrack (OldDefinitions.expandTrack path),
    OldDefinitions.proofSteps (OldDefinitions.expandTrack path), (PresentedCell.support proof.cell).card,
    PresentedCell.constructorCount proof.cell)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.RootDefinitions
