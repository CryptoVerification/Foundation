import Foundation.Examples.MixedCircuitUnifiedFusionResolution
import Foundation.Logic.Polygraph.StructuralCartesianOldExpansionCounts

/-! Bounded definitional comparison of one old contextual wire step with its
explicit eighteen-law expansion. The input is one Step, never an arbitrary
whole proof or a whole-wire normalizer. Eleven old roots and four one-hole
placements describe these instances; boundary root uses are uniformly <= 20.
This extends the partial higher basis, not its completeness. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.OldDefinitions
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Overlap
set_option backward.isDefEq.respectTransparency false
abbrev PriorBasis := StatefulWiring.basis

def macroTrack {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    RewriteTrack (relators := UnionRules) (.wire p) (.wire q) :=
  Stateful.WiringUnion.wireTrack (Cartesian.BoundedOld.expandStep change).toTrack

theorem macro_support {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    RewriteTrack.support (macroTrack change) = ∅ := Stateful.WiringUnion.wireTrack_support _

theorem oldEdit_support {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    (oldEdit change).support = ∅ := by
  simp [oldEdit, oldStep, oldPrimitive, Step.support, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, Circuit.needs]

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
      (generator : PriorBasis.Generator first second) : Generator first second
  | definition {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
      Generator (.step (oldEdit change)) (macroTrack change)

def baseBasis : HigherBasis UnionRules where
  Generator := Generator
  requirements := fun generator => match generator with
    | .existing generator => PriorBasis.requirements generator
    | .definition _ => ∅
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing generator => exact PriorBasis.covered generator
    | definition change =>
        simp only [RewriteTrack.support, oldEdit_support, macro_support]
        exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def basis : HigherBasis UnionRules := contextualBasis baseBasis

abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell basis first second

structure ExactCell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := UnionRules) p q) (footprint : Finset Nat) where
  cell : Cell first second
  support_eq : PresentedCell.support cell = footprint

def expandPrimitive {a b} {p q : Circuit signature a b} (primitive : Primitive UnionRules p q) :
    RewriteTrack (relators := UnionRules) p q := by
  cases rootView primitive with
  | oldWire change => exact macroTrack change
  | crypto stage => exact .step (oldStep (Structural.Rule.crypto stage))
  | assoc p q r => exact .step (oldStep (Structural.Rule.assoc p q r))
  | seqFusion p q => exact .step (StatefulWiring.seqFusion p q)
  | tensorFusion p q => exact .step (StatefulWiring.tensorFusion p q)
  | cryptoSuffix stage tail => exact .step (oldStep (Structural.Rule.suffix rfl stage tail))
  | wireSuffix p q tail => exact .step (Overlap.suffixStep p q tail)
  | cartesian change => exact .step (edit change)

theorem expandPrimitive_support {a b} {p q : Circuit signature a b} (change : Primitive UnionRules p q) :
    RewriteTrack.support (expandPrimitive change) = change.support := by
  cases rootView change with
  | oldWire change =>
      change RewriteTrack.support (macroTrack change) = (oldEdit change).support
      rw [macro_support, oldEdit_support]
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => rfl

def expandStep : {a b : Port signature} → {p q : Circuit signature a b} →
    Step UnionRules p q → RewriteTrack (relators := UnionRules) p q
  | _, _, _, _, .root primitive => expandPrimitive primitive
  | _, _, _, _, .seqLeft change fixed => (Placement.seqLeft fixed).track (expandStep change)
  | _, _, _, _, .seqRight fixed change => (Placement.seqRight fixed).track (expandStep change)
  | _, _, _, _, .tensorLeft change fixed => (Placement.tensorLeft fixed).track (expandStep change)
  | _, _, _, _, .tensorRight fixed change => (Placement.tensorRight fixed).track (expandStep change)

theorem expandStep_support {a b} {p q : Circuit signature a b} (change : Step UnionRules p q) :
    RewriteTrack.support (expandStep change) = change.support := by
  induction change with
  | root primitive => exact expandPrimitive_support primitive
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simp only [expandStep, Placement.track_support, ih, Placement.needs, Step.support] <;> exact Finset.union_comm _ _

def expandTrack {a b : Port signature} : {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => expandStep change
  | _, _, .comp first second => .comp (expandTrack first) (expandTrack second)
  | _, _, .inv child => .inv (expandTrack child)

theorem expandTrack_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    RewriteTrack.support (expandTrack path) = RewriteTrack.support path := by
  induction path <;> simp_all only [expandTrack, RewriteTrack.support, expandStep_support]

def eliminatePrimitive {a b} {p q : Circuit signature a b} (change : Primitive UnionRules p q) :
    ExactCell (.step (.root change)) (expandPrimitive change) change.support := by
  cases rootView change with
  | oldWire change =>
      refine ⟨.generator (.root (.definition change)), ?_⟩
      change ∅ = (oldEdit change).support
      exact (oldEdit_support change).symm
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => exact ⟨.refl _, rfl⟩

def eliminateStep : {a b : Port signature} → {p q : Circuit signature a b} → (change : Step UnionRules p q) →
    ExactCell (.step change) (expandStep change) change.support
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
    ExactCell path (expandTrack path) (RewriteTrack.support path)
  | _, _, .refl p => ⟨.refl _, rfl⟩
  | _, _, .step change => eliminateStep change
  | _, _, .comp first second =>
      let one := eliminateTrack first
      let two := eliminateTrack second
      ⟨.comp one.cell two.cell, by simp only [PresentedCell.support, one.support_eq, two.support_eq, RewriteTrack.support]⟩
  | _, _, .inv child =>
      let proof := eliminateTrack child
      ⟨.inverse proof.cell, by simp only [PresentedCell.support, proof.support_eq, RewriteTrack.support]⟩

/-- Retain previous higher proofs compositionally, not as whole-cell roots. -/
def embedPrior {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → PresentedCell PriorBasis first second → Cell first second
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedPrior child).symm
  | _, _, _, _, .trans first second => (embedPrior first).trans (embedPrior second)
  | _, _, _, _, .comp first second => .comp (embedPrior first) (embedPrior second)
  | _, _, _, _, .inverse child => .inverse (embedPrior child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit p => .leftUnit p
  | _, _, _, _, .rightUnit p => .rightUnit p
  | _, _, _, _, .leftInv p => .leftInv p
  | _, _, _, _, .rightInv p => .rightInv p

theorem embedPrior_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    PresentedCell.support (embedPrior cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedPrior, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support, baseBasis]

theorem embedPrior_count {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    PresentedCell.constructorCount (embedPrior cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [embedPrior, PresentedCell.constructorCount]

/-- Only the boundary tracks are eliminated. The comparison may still use
old-library generators internally; this is not a smaller-basis projection. -/
def expandComparison {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    Cell (expandTrack first) (expandTrack second) :=
  (eliminateTrack first).cell.symm.trans ((embedPrior cell).trans (eliminateTrack second).cell)

theorem expandComparison_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    PresentedCell.support (expandComparison cell) = PresentedCell.support cell := by
  simp only [expandComparison, PresentedCell.support, embedPrior_support,
    (eliminateTrack first).support_eq, (eliminateTrack second).support_eq]
  rw [Finset.union_eq_left.mpr cell.boundaries.2, Finset.union_eq_right.mpr cell.boundaries.1]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.OldDefinitions
