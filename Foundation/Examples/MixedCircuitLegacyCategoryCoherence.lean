import Foundation.Examples.MixedCircuitLegacyWireBasis
import Foundation.Logic.Polygraph.StructuralCartesianLegacyComposition

/-! Legacy and eighteen-law encodings of parallel source composition proofs
are compared in one actual mixed presentation. All old/new bridges use the
existing eleven ROOT definitions and derived context lifting. This does not
assert coherence for arbitrary legacy or cartesian proof paths. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyCategoryCoherence
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher.CategoryCritical
open Stateful.WiringUnion
open LegacyWireBasis
set_option backward.isDefEq.respectTransparency false
variable {E : Port signature → Port signature → Type}

def legacy (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    RewriteTrack (relators := UnionRules) (.wire (CompositionTransport.evaluate interpret p))
      (.wire (CompositionTransport.evaluate interpret q)) :=
  (CompositionTransport.Legacy.track interpret path).map Circuit.wire
    (fun change => StatefulWiring.Overlap.oldEdit change)

def current (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    RewriteTrack (relators := UnionRules) (.wire (CompositionTransport.evaluate interpret p))
      (.wire (CompositionTransport.evaluate interpret q)) :=
  wireTrack (original := Structural.Fusion.rules) (CompositionTransport.track interpret path)

theorem legacy_occurrences (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    StatefulWiring.OldDefinitions.legacyTrack (legacy interpret path) = Cartesian.BoundedOld.steps path := by
  induction path with
  | refl => rfl
  | step change => rfl
  | comp first second ih₁ ih₂ =>
      simpa only [legacy, CompositionTransport.Legacy.track, Track.map,
        StatefulWiring.OldDefinitions.legacyTrack, Cartesian.BoundedOld.steps] using congrArg₂ (· + ·) ih₁ ih₂
  | inv child ih => exact ih

theorem current_clean (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    StatefulWiring.OldDefinitions.legacyTrack (current interpret path) = 0 :=
  StatefulWiring.OldDefinitions.legacy_wireTrack _

def pureLift {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) : Cell (wireTrack first) (wireTrack second) :=
  currentLift (CategoryWirePass.categoryLift
    (CartesianCategoryCritical.embedPure Structural.Fusion.basis (oldLift cell)))

theorem pureLift_support {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) : PresentedCell.support (pureLift cell) = ∅ := by
  rw [pureLift, currentLift_support, CategoryWirePass.categoryLift_support, CartesianCategoryCritical.embedPure_support]

theorem pureLift_definitions {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) : definitions (pureLift cell) = 0 := currentLift_definitions _

def bridgeStep (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (change : Composition.Expr.Step p q) :
    Cell (legacy interpret (.step change)) (current interpret (.step change)) :=
  (legacyLift (StatefulWiring.RootDefinitions.eliminateWireStep (CompositionTransport.Legacy.edge interpret change))).trans
    (pureLift (CompositionTransport.Legacy.expansion interpret change))

theorem bridgeStep_support (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (change : Composition.Expr.Step p q) :
    PresentedCell.support (bridgeStep interpret change) = ∅ := by
  simp only [bridgeStep, PresentedCell.support, legacyLift_support,
    StatefulWiring.RootDefinitions.eliminateWireStep_support, pureLift_support, Finset.union_empty]

theorem bridgeStep_definitions (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (change : Composition.Expr.Step p q) :
    definitions (bridgeStep interpret change) = 1 := by
  simp only [bridgeStep, definitions, legacyLift_definitions,
    StatefulWiring.RootDefinitions.eliminateWireStep_definitions, pureLift_definitions, Nat.add_zero]

def bridge (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature} :
    {p q : Composition.Expr E a b} → (path : Composition.Finite.Three p q) →
    Cell (legacy interpret path) (current interpret path)
  | _, _, .refl _ => .refl _
  | _, _, .step change => bridgeStep interpret change
  | _, _, .comp first second => .comp (bridge interpret first) (bridge interpret second)
  | _, _, .inv child => .inverse (bridge interpret child)

theorem bridge_support (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    PresentedCell.support (bridge interpret path) = ∅ := by
  induction path with
  | refl => rfl
  | step change => exact bridgeStep_support interpret change
  | comp first second ih₁ ih₂ => simp only [bridge, PresentedCell.support, ih₁, ih₂, Finset.union_empty]
  | inv child ih => exact ih

theorem bridge_definitions (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    definitions (bridge interpret path) = Cartesian.BoundedOld.steps path := by
  induction path <;> simp_all only [bridge, bridgeStep_definitions, definitions, Cartesian.BoundedOld.steps]

def currentComparison (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :=
  currentLift (CategoryWirePass.compositionComparison interpret first second)

theorem currentComparison_support (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    PresentedCell.support (currentComparison interpret first second) = ∅ := by
  rw [currentComparison, currentLift_support, CategoryWirePass.compositionComparison_support]

def mixedCoherence (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    Cell (legacy interpret first) (current interpret second) :=
  (bridge interpret first).trans (currentComparison interpret first second)

def legacyCoherence (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    Cell (legacy interpret first) (legacy interpret second) :=
  (mixedCoherence interpret first second).trans (bridge interpret second).symm

theorem mixedCoherence_support (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    PresentedCell.support (mixedCoherence interpret first second) = ∅ := by
  simp only [mixedCoherence, PresentedCell.support, bridge_support, currentComparison_support, Finset.union_empty]

theorem legacyCoherence_support (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    PresentedCell.support (legacyCoherence interpret first second) = ∅ := by
  simp only [legacyCoherence, PresentedCell.support, mixedCoherence_support, bridge_support, Finset.union_empty]

theorem mixedCoherence_definitions (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    definitions (mixedCoherence interpret first second) = Cartesian.BoundedOld.steps first := by
  simp only [mixedCoherence, currentComparison, definitions, bridge_definitions, currentLift_definitions, Nat.add_zero]

theorem legacyCoherence_definitions (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q) :
    definitions (legacyCoherence interpret first second) =
      Cartesian.BoundedOld.steps first + Cartesian.BoundedOld.steps second := by
  simp only [legacyCoherence, definitions, mixedCoherence_definitions, bridge_definitions]

theorem bridge_matches_legacy_occurrences (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b : Port signature}
    {p q : Composition.Expr E a b} (path : Composition.Finite.Three p q) :
    definitions (bridge interpret path) = StatefulWiring.OldDefinitions.legacyTrack (legacy interpret path) :=
  (bridge_definitions interpret path).trans (legacy_occurrences interpret path).symm

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyCategoryCoherence
