import Foundation.Examples.MixedCircuitCategoryWirePass
import Foundation.Examples.MixedCircuitRootWireElimination
import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigherBasisSumCounts

/-! Combine the current categorical/MAC presentation with the existing
ROOT-ONLY eleven-law definitions. Arbitrary contextual old-step definitions
are not imported as generators. The old elimination algorithm is reused;
its support, cleanliness, root bound and exact definition count are retained. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyWireBasis
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
set_option backward.isDefEq.respectTransparency false
abbrev UnionRules := PresentedWirePass.UnionRules
abbrev RootBasis := StatefulWiring.RootDefinitions.basis
def presentation : HigherBasis UnionRules := (contextualBasis CategoryWirePass.presentation).sum RootBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def currentLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : CategoryWirePass.Cell first second) : Cell first second := (cell.injectLeft RootBasis).embed

def legacyLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.RootDefinitions.Cell first second) : Cell first second :=
  (cell.injectRight (contextualBasis CategoryWirePass.presentation)).embed

theorem currentLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : CategoryWirePass.Cell first second) : PresentedCell.support (currentLift cell) = PresentedCell.support cell := by
  rw [currentLift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

theorem legacyLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.RootDefinitions.Cell first second) : PresentedCell.support (legacyLift cell) = PresentedCell.support cell := by
  rw [legacyLift, PresentedCell.embed_support, PresentedCell.injectRight_support]

theorem currentLift_constructorCount {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : CategoryWirePass.Cell first second) : PresentedCell.constructorCount (currentLift cell) = PresentedCell.constructorCount cell := by
  rw [currentLift, PresentedCell.embed_constructorCount, PresentedCell.injectLeft_constructorCount]

theorem legacyLift_constructorCount {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.RootDefinitions.Cell first second) : PresentedCell.constructorCount (legacyLift cell) = PresentedCell.constructorCount cell := by
  rw [legacyLift, PresentedCell.embed_constructorCount, PresentedCell.injectRight_constructorCount]

def generatorDefinitions : {a b : Port signature} → {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → ContextualGenerator presentation first second → Nat
  | _, _, _, _, _, _, .root (.inl _) => 0
  | _, _, _, _, _, _, .root (.inr old) => StatefulWiring.RootDefinitions.generatorDefinitions old
  | _, _, _, _, _, _, .placed _ child => generatorDefinitions child

def definitions {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → Cell first second → Nat
  | _, _, _, _, .generator generator => generatorDefinitions generator
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => definitions child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => definitions first + definitions second
  | _, _, _, _, _ => 0

theorem currentLift_definitions {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : CategoryWirePass.Cell first second) : definitions (currentLift cell) = 0 := by
  induction cell <;> simp_all only [currentLift, PresentedCell.injectLeft, PresentedCell.embed,
    definitions, generatorDefinitions, Nat.add_zero]

theorem legacyLift_definitions {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : StatefulWiring.RootDefinitions.Cell first second) :
    definitions (legacyLift cell) = StatefulWiring.RootDefinitions.definitions cell := by
  induction cell <;> simp_all only [legacyLift, PresentedCell.injectRight, PresentedCell.embed,
    definitions, generatorDefinitions, StatefulWiring.RootDefinitions.definitions]

theorem definitions_whisker {a b c d} (place : Placement (signature := signature) a b c d)
    {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q} (cell : Cell first second) :
    definitions (cell.whisker place) = definitions cell := by
  induction cell <;> simp_all only [PresentedCell.whisker, definitions, generatorDefinitions]

def eliminate {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    { cell : Cell path (StatefulWiring.OldDefinitions.expandTrack path) // PresentedCell.support cell = path.support } :=
  ⟨legacyLift (StatefulWiring.RootDefinitions.eliminateTrack path).cell,
    (legacyLift_support _).trans (StatefulWiring.RootDefinitions.eliminateTrack path).support_eq⟩

theorem eliminate_definitions {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    definitions (eliminate path).val = StatefulWiring.OldDefinitions.legacyTrack path :=
  (legacyLift_definitions _).trans (StatefulWiring.RootDefinitions.eliminateTrack_definitions path)

theorem eliminate_constructorCount {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    PresentedCell.constructorCount (eliminate path).val =
      PresentedCell.constructorCount (StatefulWiring.RootDefinitions.eliminateTrack path).cell := legacyLift_constructorCount _

theorem expanded_clean {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    StatefulWiring.OldDefinitions.legacyTrack (StatefulWiring.OldDefinitions.expandTrack path) = 0 :=
  StatefulWiring.OldDefinitions.expandTrack_clean path

theorem expanded_steps {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    Cartesian.BoundedOld.steps (StatefulWiring.OldDefinitions.expandTrack path) ≤ 20 * Cartesian.BoundedOld.steps path :=
  StatefulWiring.OldDefinitions.expandTrack_steps path

theorem expandStep_fixed {a b} {p q : Circuit signature a b} (change : Step UnionRules p q)
    (clean : StatefulWiring.OldDefinitions.legacyStep change = 0) :
    StatefulWiring.OldDefinitions.expandStep change = .step change := by
  induction change with
  | root primitive =>
      cases StatefulWiring.Overlap.rootView primitive with
      | oldWire old =>
          change 1 = 0 at clean
          omega
      | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => rfl
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [StatefulWiring.OldDefinitions.expandStep, ih clean, Placement.track, Track.map, Placement.step]

theorem expandTrack_fixed {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q)
    (clean : StatefulWiring.OldDefinitions.legacyTrack path = 0) :
    StatefulWiring.OldDefinitions.expandTrack path = path := by
  induction path with
  | refl => rfl
  | step change => exact expandStep_fixed change clean
  | comp first second ih₁ ih₂ =>
      have both := Nat.add_eq_zero_iff.mp clean
      exact congrArg₂ Track.comp (ih₁ both.1) (ih₂ both.2)
  | inv child ih => exact congrArg Track.inv (ih clean)

theorem expansion_idempotent {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    StatefulWiring.OldDefinitions.expandTrack (StatefulWiring.OldDefinitions.expandTrack path) =
      StatefulWiring.OldDefinitions.expandTrack path :=
  expandTrack_fixed _ (expanded_clean path)

def expandComparison {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : Cell first second) :
    Cell (StatefulWiring.OldDefinitions.expandTrack first) (StatefulWiring.OldDefinitions.expandTrack second) :=
  (eliminate first).val.symm.trans (cell.trans (eliminate second).val)

theorem expandComparison_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : Cell first second) : PresentedCell.support (expandComparison cell) = PresentedCell.support cell := by
  simp only [expandComparison, PresentedCell.support, (eliminate first).property, (eliminate second).property]
  rw [Finset.union_eq_left.mpr cell.boundaries.2, Finset.union_eq_right.mpr cell.boundaries.1]

def recoverComparison {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : Cell (StatefulWiring.OldDefinitions.expandTrack first) (StatefulWiring.OldDefinitions.expandTrack second)) :
    Cell first second := (eliminate first).val.trans (cell.trans (eliminate second).val.symm)

theorem recoverComparison_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (cell : Cell (StatefulWiring.OldDefinitions.expandTrack first) (StatefulWiring.OldDefinitions.expandTrack second)) :
    PresentedCell.support (recoverComparison cell) = PresentedCell.support cell := by
  have bounds := cell.boundaries
  simp only [StatefulWiring.OldDefinitions.expandTrack_support] at bounds
  simp only [recoverComparison, PresentedCell.support, (eliminate first).property, (eliminate second).property]
  rw [Finset.union_eq_left.mpr bounds.2, Finset.union_eq_right.mpr bounds.1]

theorem comparison_iff_expanded {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :
    Nonempty (Cell first second) ↔
      Nonempty (Cell (StatefulWiring.OldDefinitions.expandTrack first) (StatefulWiring.OldDefinitions.expandTrack second)) :=
  ⟨fun ⟨cell⟩ => ⟨expandComparison cell⟩, fun ⟨cell⟩ => ⟨recoverComparison cell⟩⟩

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyWireBasis
