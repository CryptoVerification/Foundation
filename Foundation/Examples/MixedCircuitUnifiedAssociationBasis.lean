import Foundation.Examples.MixedCircuitRootWireElimination
import Foundation.Examples.MixedCircuitSuffixOverlap

/-! Three explicit single-change association naturality forms for the whole
unified rule type. Both boundaries contain two steps. Previous root-only
wire definitions and local diagrams remain available compositionally. This
is a partial higher extension, not a whole-path comparison generator. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Overlap
set_option backward.isDefEq.respectTransparency false
abbrev PriorBasis := RootDefinitions.basis

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
      (generator : PriorBasis.Generator first second) : Generator first second
  | first {a b c d} {p p' : Circuit signature a b} (change : Step UnionRules p p')
      (q : Circuit signature b c) (r : Circuit signature c d) :
      Generator (two (.seqLeft (.seqLeft change q) r) (associate p' q r))
        (two (associate p q r) (.seqLeft change (.seq q r)))
  | middle {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
      (change : Step UnionRules q q') (r : Circuit signature c d) :
      Generator (two (.seqLeft (.seqRight p change) r) (associate p q' r))
        (two (associate p q r) (.seqRight p (.seqLeft change r)))
  | last {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
      {r r' : Circuit signature c d} (change : Step UnionRules r r') :
      Generator (two (.seqRight (.seq p q) change) (associate p q r'))
        (two (associate p q r) (.seqRight p (.seqRight q change)))

def baseBasis : HigherBasis UnionRules where
  Generator := Generator
  requirements := fun {_ _ _ _ first second} generator => match generator with
    | .existing old => PriorBasis.requirements old
    | _ => RewriteTrack.support first ∪ RewriteTrack.support second
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing old => exact PriorBasis.covered old
    | first | middle | last => exact ⟨Finset.subset_union_left, Finset.subset_union_right⟩

def basis : HigherBasis UnionRules := contextualBasis baseBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell basis first second

def embedRoot {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → PresentedCell PriorBasis first second → Cell first second
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedRoot child).symm
  | _, _, _, _, .trans first second => (embedRoot first).trans (embedRoot second)
  | _, _, _, _, .comp first second => .comp (embedRoot first) (embedRoot second)
  | _, _, _, _, .inverse child => .inverse (embedRoot child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit p => .leftUnit p
  | _, _, _, _, .rightUnit p => .rightUnit p
  | _, _, _, _, .leftInv p => .leftInv p
  | _, _, _, _, .rightInv p => .rightInv p

theorem embedRoot_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell PriorBasis first second) :
    PresentedCell.support (embedRoot cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedRoot, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support, baseBasis]

def fromFusion {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := Structural.Fusion.rules) p q} (cell : Structural.Fusion.Cell first second) :
    Cell (Stateful.WiringUnion.embedTrack first) (Stateful.WiringUnion.embedTrack second) :=
  embedRoot (RootDefinitions.embedPrior (embedOld (Stateful.WiringUnion.embedCell cell)))

def fromStructural {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @Structural.rules true) p q} (cell : Structural.MixedCell first second) :
    Cell (Stateful.WiringUnion.embedTrack (Structural.Fusion.embedTrack first))
      (Stateful.WiringUnion.embedTrack (Structural.Fusion.embedTrack second)) := fromFusion (Structural.Fusion.embedCell cell)

theorem fromFusion_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := Structural.Fusion.rules) p q} (cell : Structural.Fusion.Cell first second) :
    PresentedCell.support (fromFusion cell) = PresentedCell.support cell := by
  rw [fromFusion, embedRoot_support, RootDefinitions.embedPrior_support, embedOld_support, Stateful.WiringUnion.embedCell_support]

theorem fromStructural_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @Structural.rules true) p q} (cell : Structural.MixedCell first second) :
    PresentedCell.support (fromStructural cell) = PresentedCell.support cell := by
  rw [fromStructural, fromFusion_support, Structural.Fusion.embedCell_support]

theorem fromFusion_count {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := Structural.Fusion.rules) p q} (cell : Structural.Fusion.Cell first second) :
    PresentedCell.constructorCount (fromFusion cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [fromFusion, embedRoot, RootDefinitions.embedPrior, embedOld,
    Stateful.WiringUnion.embedCell, PresentedCell.constructorCount]

theorem fromStructural_count {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @Structural.rules true) p q} (cell : Structural.MixedCell first second) :
    PresentedCell.constructorCount (fromStructural cell) = PresentedCell.constructorCount cell := by
  rw [fromStructural, fromFusion_count, Structural.Fusion.embedCell_constructorCount]

def firstNaturality {a b c d} {p p' : Circuit signature a b} (change : Step UnionRules p p')
    (q : Circuit signature b c) (r : Circuit signature c d) :
    Cell (two (.seqLeft (.seqLeft change q) r) (associate p' q r))
      (two (associate p q r) (.seqLeft change (.seq q r))) := .generator (.root (.first change q r))

def middleNaturality {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
    (change : Step UnionRules q q') (r : Circuit signature c d) :
    Cell (two (.seqLeft (.seqRight p change) r) (associate p q' r))
      (two (associate p q r) (.seqRight p (.seqLeft change r))) := .generator (.root (.middle p change r))

def lastNaturality {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
    {r r' : Circuit signature c d} (change : Step UnionRules r r') :
    Cell (two (.seqRight (.seq p q) change) (associate p q r'))
      (two (associate p q r) (.seqRight p (.seqRight q change))) := .generator (.root (.last p q change))

theorem associate_support {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
    (associate p q r).support = p.needs ∪ q.needs ∪ r.needs := by
  simp [associate, oldStep, oldPrimitive, Step.support, Primitive.support, Relator.support, UnionRules,
    Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, Circuit.needs,
    Finset.union_assoc, Finset.union_comm]


end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
