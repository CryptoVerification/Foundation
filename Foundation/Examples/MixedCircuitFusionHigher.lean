import Foundation.Examples.MixedCircuitFusionCompletion

/-! A context-closed coherent definition for suffix wire fusion. Existing
local generators remain explicit data; an old whole-cell is never made a new
generator. Every new proof track admits guard-preserving macro elimination. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := rules) p q → RewriteTrack (relators := rules) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := @Structural.rules true) p q}
      (generator : ContextualGenerator Structural.localBasis first second) : Generator (embedTrack first) (embedTrack second)
  | definition {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
      Generator (.step (suffixStep p q tail))
        (embedTrack (.comp (.inv (.step (associate (.wire p) (.wire q) tail))) (.step (.seqLeft (seqFusion p q) tail))))

def baseBasis : HigherBasis rules where
  Generator := Generator
  requirements := fun generator => match generator with
    | .existing old => old.support
    | .definition _ _ tail => tail.needs
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing old =>
        simp only [embedTrack_support]
        exact old.boundaries
    | definition p q tail =>
        simp [embedTrack_support, RewriteTrack.support, suffixStep_support, associate,
          seqFusion, Step.support, Primitive.support, Relator.support, Structural.rules, Circuit.needs]

def basis : HigherBasis rules := contextualBasis baseBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := rules) p q) :=
  PresentedCell basis first second

def embedCell {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := @Structural.rules true) p q} → MixedCell first second →
      Cell (embedTrack first) (embedTrack second)
  | _, _, _, _, .refl p => .refl (embedTrack p)
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedCell child).symm
  | _, _, _, _, .trans first second => (embedCell first).trans (embedCell second)
  | _, _, _, _, .comp first second => .comp (embedCell first) (embedCell second)
  | _, _, _, _, .inverse child => .inverse (embedCell child)
  | _, _, _, _, .assoc p q r => .assoc (embedTrack p) (embedTrack q) (embedTrack r)
  | _, _, _, _, .leftUnit p => .leftUnit (embedTrack p)
  | _, _, _, _, .rightUnit p => .rightUnit (embedTrack p)
  | _, _, _, _, .leftInv p => .leftInv (embedTrack p)
  | _, _, _, _, .rightInv p => .rightInv (embedTrack p)

theorem embedCell_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @Structural.rules true) p q} (cell : MixedCell first second) :
    PresentedCell.support (embedCell cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedCell, PresentedCell.support, embedTrack_support,
    basis, baseBasis, contextualBasis, ContextualGenerator.support, Structural.mixedBasis]

theorem embedCell_constructorCount {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @Structural.rules true) p q} (cell : MixedCell first second) :
    PresentedCell.constructorCount (embedCell cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [embedCell, PresentedCell.constructorCount]

/-- Carry the footprint equality through dependent boundary transports. -/
structure ExactCell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := rules) p q) (footprint : Finset Nat) where
  cell : Cell first second
  support_eq : PresentedCell.support cell = footprint

def eliminatePrimitive {a b} {p q : Circuit signature a b} (change : Primitive rules p q) :
    ExactCell (.step (.root change)) (embedTrack (expandPrimitive change)) change.support := by
  cases change with
  | rule label =>
      cases label with
      | existing label => exact ⟨.refl _, rfl⟩
      | suffix p q tail =>
          refine ⟨.generator (.root (.definition p q tail)), ?_⟩
          simp [PresentedCell.support, basis, contextualBasis, ContextualGenerator.support,
            baseBasis, Primitive.support, Relator.support, rules, Circuit.needs]

def eliminateStep : {a b : Port signature} → {p q : Circuit signature a b} → (change : Step rules p q) →
    ExactCell (.step change) (embedTrack (expandStep change)) change.support
  | _, _, _, _, .root change => eliminatePrimitive change
  | _, _, _, _, .seqLeft change fixed => by
      simp only [expandStep, embedTrack_placement]
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.seqLeft fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support]
  | _, _, _, _, .seqRight fixed change => by
      simp only [expandStep, embedTrack_placement]
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.seqRight fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support, Finset.union_comm]
  | _, _, _, _, .tensorLeft change fixed => by
      simp only [expandStep, embedTrack_placement]
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.tensorLeft fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support]
  | _, _, _, _, .tensorRight fixed change => by
      simp only [expandStep, embedTrack_placement]
      let child := eliminateStep change
      refine ⟨child.cell.whisker (Placement.tensorRight fixed), ?_⟩
      simp only [PresentedCell.whisker_support, child.support_eq, Placement.needs, Step.support, Finset.union_comm]

def eliminateTrack {a b : Port signature} : {p q : Circuit signature a b} → (path : RewriteTrack (relators := rules) p q) →
    ExactCell path (embedTrack (expandTrack path)) (RewriteTrack.support path)
  | _, _, .refl p => ⟨.refl _, rfl⟩
  | _, _, .step change => eliminateStep change
  | _, _, .comp first second =>
      let one := eliminateTrack first
      let two := eliminateTrack second
      ⟨.comp one.cell two.cell, by simp only [PresentedCell.support, RewriteTrack.support, one.support_eq, two.support_eq]⟩
  | _, _, .inv child =>
      let one := eliminateTrack child
      ⟨.inverse one.cell, one.support_eq⟩

theorem eliminateTrack_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    PresentedCell.support (eliminateTrack path).cell = RewriteTrack.support path := (eliminateTrack path).support_eq

def criticalCell {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Cell (.comp (.step (embedStep (associate (.wire p) (.wire q) tail))) (.step (suffixStep p q tail)))
      (.step (embedStep (.seqLeft (seqFusion p q) tail))) :=
  (Four.comp (.refl _) (.generator (.root (.definition p q tail)))).trans
    ((Four.assoc _ _ _).symm.trans
      ((Four.comp (Four.rightInv _) (.refl _)).trans (Four.leftUnit _)))

theorem criticalCell_support {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.support (criticalCell p q tail) = tail.needs := by
  simp [criticalCell, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support,
    baseBasis, RewriteTrack.support, embedStep_support, associate, seqFusion,
    Step.support, Primitive.support, Relator.support, Structural.rules, Circuit.needs]

theorem criticalCell_constructorCount {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.constructorCount (criticalCell p q tail) = 12 := by rfl

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
