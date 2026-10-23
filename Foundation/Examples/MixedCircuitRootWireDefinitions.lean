import Foundation.Examples.MixedCircuitWireFrameNaturality
import Foundation.Examples.MixedCircuitOldWireDefinitions

/-! Only the eleven context-free old roots are new definition generators.
Internal contexts are derived using existing fusion naturality and groupoid
cancellation. The prior contextual-definition basis is NOT included here. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.RootDefinitions
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Overlap
open WireFrame
set_option backward.isDefEq.respectTransparency false
abbrev PriorBasis := StatefulWiring.basis

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
      (generator : PriorBasis.Generator first second) : Generator first second
  | definition {a b} {p q : Wiring signature a b} (root : Rewrite.Root p q) :
      Generator (.step (oldEdit (.root root))) (OldDefinitions.macroTrack (.root root))

def baseBasis : HigherBasis UnionRules where
  Generator := Generator
  requirements := fun generator => match generator with
    | .existing generator => PriorBasis.requirements generator
    | .definition _ => ∅
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing generator => exact PriorBasis.covered generator
    | definition root =>
        simp only [RewriteTrack.support, OldDefinitions.oldEdit_support, OldDefinitions.macro_support]
        exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def basis : HigherBasis UnionRules := contextualBasis baseBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell basis first second

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

def liftComparison {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (change : Structural.WireEdit p q) (path : Cartesian.ProofTrack p q)
    (child : Cell (.step (oldEdit change)) (Stateful.WiringUnion.wireTrack path)) :
    Cell (.step (oldEdit (frame.oldStep change))) (Stateful.WiringUnion.wireTrack (frame.cartTrack path)) :=
  FourNaturality.cancelPrefix (.step (frame.fusion p))
    ((embedPrior (frame.oldNaturality change)).symm.trans
      ((Four.comp (child.whisker frame.place) (.refl (.step (frame.fusion q)))).trans
        (embedPrior (frame.cartNaturality path))))

theorem macro_seqLeft {a b c} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature b c) :
    OldDefinitions.macroTrack (.seqLeft change q) =
      .comp (Stateful.WiringUnion.wireTrack ((Frame.seqLeft q).cartTrack (Cartesian.BoundedOld.expandStep change).toTrack))
        (.refl _) := rfl

theorem macro_seqRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Structural.WireEdit q q') :
    OldDefinitions.macroTrack (.seqRight p change) =
      .comp (.refl _)
        (Stateful.WiringUnion.wireTrack ((Frame.seqRight p).cartTrack (Cartesian.BoundedOld.expandStep change).toTrack)) := rfl

theorem macro_tensorLeft {a b c d} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature c d) :
    OldDefinitions.macroTrack (.tensorLeft change q) =
      .comp (Stateful.WiringUnion.wireTrack ((Frame.tensorLeft q).cartTrack (Cartesian.BoundedOld.expandStep change).toTrack))
        (.refl _) := rfl

theorem macro_tensorRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Structural.WireEdit q q') :
    OldDefinitions.macroTrack (.tensorRight p change) =
      .comp (.refl _)
        (Stateful.WiringUnion.wireTrack ((Frame.tensorRight p).cartTrack (Cartesian.BoundedOld.expandStep change).toTrack)) := rfl

def castRight {a b} {p q : Circuit signature a b} {first second third : RewriteTrack (relators := UnionRules) p q}
    (same : second = third) (cell : Cell first second) : Cell first third := same ▸ cell

theorem castRight_support {a b} {p q : Circuit signature a b} {first second third : RewriteTrack (relators := UnionRules) p q}
    (same : second = third) (cell : Cell first second) :
    PresentedCell.support (castRight same cell) = PresentedCell.support cell := by cases same; rfl

def eliminateWireStep : {a b : Port signature} → {p q : Wiring signature a b} → (change : Structural.WireEdit p q) →
    Cell (.step (oldEdit change)) (OldDefinitions.macroTrack change)
  | _, _, _, _, .root root => .generator (.root (.definition root))
  | _, _, _, _, .seqLeft change fixed =>
      castRight (macro_seqLeft change fixed).symm
        ((liftComparison (.seqLeft fixed) change _ (eliminateWireStep change)).trans (Four.rightUnit _).symm)
  | _, _, _, _, .seqRight fixed change =>
      castRight (macro_seqRight fixed change).symm
        ((liftComparison (.seqRight fixed) change _ (eliminateWireStep change)).trans (Four.leftUnit _).symm)
  | _, _, _, _, .tensorLeft change fixed =>
      castRight (macro_tensorLeft change fixed).symm
        ((liftComparison (.tensorLeft fixed) change _ (eliminateWireStep change)).trans (Four.rightUnit _).symm)
  | _, _, _, _, .tensorRight fixed change =>
      castRight (macro_tensorRight fixed change).symm
        ((liftComparison (.tensorRight fixed) change _ (eliminateWireStep change)).trans (Four.leftUnit _).symm)

theorem liftComparison_support {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (change : Structural.WireEdit p q) (path : Cartesian.ProofTrack p q)
    (child : Cell (.step (oldEdit change)) (Stateful.WiringUnion.wireTrack path))
    (empty : PresentedCell.support child = ∅) :
    PresentedCell.support (liftComparison frame change path child) = ∅ := by
  simp only [liftComparison, FourNaturality.cancelPrefix, FourNaturality.undoInversePrefix,
    PresentedCell.support, RewriteTrack.support, embedPrior_support, Frame.oldNaturality_support,
    Frame.cartNaturality_support, PresentedCell.whisker_support, empty, Frame.place_needs,
    Frame.fusion_support, OldDefinitions.oldEdit_support, Stateful.WiringUnion.wireTrack_support, Finset.union_empty]

theorem eliminateWireStep_support {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    PresentedCell.support (eliminateWireStep change) = ∅ := by
  induction change with
  | root root => rfl
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [eliminateWireStep, castRight_support, PresentedCell.support, liftComparison_support _ _ _ _ ih, Stateful.WiringUnion.wireTrack_support, Finset.union_empty]

def generatorDefinitions : {a b : Port signature} → {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → ContextualGenerator baseBasis first second → Nat
  | _, _, _, _, _, _, .root (.existing _) => 0
  | _, _, _, _, _, _, .root (.definition _) => 1
  | _, _, _, _, _, _, .placed _ child => generatorDefinitions child

def definitions {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → Cell first second → Nat
  | _, _, _, _, .generator generator => generatorDefinitions generator
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => definitions child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => definitions first + definitions second
  | _, _, _, _, _ => 0

theorem definitions_whisker {a b c d} (place : Placement (signature := signature) a b c d)
    {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q} (cell : Cell first second) :
    definitions (cell.whisker place) = definitions cell := by
  induction cell <;> simp_all only [PresentedCell.whisker, definitions, generatorDefinitions]

theorem embedPrior_definitions {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    definitions (embedPrior cell) = 0 := by
  induction cell <;> simp_all only [embedPrior, definitions, generatorDefinitions, Nat.add_zero]

theorem castRight_definitions {a b} {p q : Circuit signature a b} {first second third : RewriteTrack (relators := UnionRules) p q}
    (same : second = third) (cell : Cell first second) : definitions (castRight same cell) = definitions cell := by cases same; rfl

theorem liftComparison_definitions {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (change : Structural.WireEdit p q) (path : Cartesian.ProofTrack p q)
    (child : Cell (.step (oldEdit change)) (Stateful.WiringUnion.wireTrack path)) :
    definitions (liftComparison frame change path child) = definitions child := by
  simp only [liftComparison, FourNaturality.cancelPrefix, FourNaturality.undoInversePrefix,
    definitions, embedPrior_definitions, definitions_whisker, Nat.zero_add, Nat.add_zero]

theorem eliminateWireStep_definitions {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    definitions (eliminateWireStep change) = 1 := by
  induction change with
  | root root => rfl
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [eliminateWireStep, castRight_definitions, definitions, liftComparison_definitions, ih, Nat.add_zero]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.RootDefinitions
