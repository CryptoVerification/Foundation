import Foundation.Examples.MixedCircuitOldWireDefinitions

/-! Elimination is syntactic, not just equality of endpoints: no old wire
rule remains, root-occurrence growth is at most 20, and all guards are retained.
Counts include inverse equality uses but exclude payload and runtime costs. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.OldDefinitions
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Overlap
set_option backward.isDefEq.respectTransparency false
abbrev proofSteps := @Cartesian.BoundedOld.steps

/-- Count exactly the old-wire primitive label, including under contexts. -/
def legacyPrimitive {a b} {p q : Circuit signature a b} (primitive : Primitive UnionRules p q) : Nat := by
  cases rootView primitive with
  | oldWire => exact 1
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => exact 0

def legacyStep : {a b : Port signature} → {p q : Circuit signature a b} → Step UnionRules p q → Nat
  | _, _, _, _, .root primitive => legacyPrimitive primitive
  | _, _, _, _, .seqLeft change _ | _, _, _, _, .seqRight _ change
  | _, _, _, _, .tensorLeft change _ | _, _, _, _, .tensorRight _ change => legacyStep change

def legacyTrack {a b : Port signature} : {p q : Circuit signature a b} → RewriteTrack (relators := UnionRules) p q → Nat
  | _, _, .refl _ => 0
  | _, _, .step change => legacyStep change
  | _, _, .comp first second => legacyTrack first + legacyTrack second
  | _, _, .inv child => legacyTrack child

theorem legacy_wireTrack {a b} {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    legacyTrack (Stateful.WiringUnion.wireTrack (original := Structural.Fusion.rules) path) = 0 := by
  induction path with
  | refl => rfl
  | step => rfl
  | comp first second one two =>
      simp only [Stateful.WiringUnion.wireTrack, Track.map, legacyTrack] at *
      rw [one, two, Nat.add_zero]
  | inv child ih => exact ih

theorem legacy_placement {a b c d} (place : Placement (signature := signature) a b c d)
    {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    legacyTrack (place.track path) = legacyTrack path := by
  cases place <;> induction path <;>
    simp_all only [Placement.track, Track.map, legacyTrack, Placement.step, legacyStep]

theorem expandPrimitive_clean {a b} {p q : Circuit signature a b} (primitive : Primitive UnionRules p q) :
    legacyTrack (expandPrimitive primitive) = 0 := by
  cases rootView primitive with
  | oldWire change => exact legacy_wireTrack _
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian => rfl

theorem expandStep_clean {a b} {p q : Circuit signature a b} (change : Step UnionRules p q) :
    legacyTrack (expandStep change) = 0 := by
  induction change with
  | root primitive => exact expandPrimitive_clean primitive
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simpa only [expandStep, legacy_placement] using ih

theorem expandTrack_clean {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    legacyTrack (expandTrack path) = 0 := by
  induction path with
  | refl => rfl
  | step change => exact expandStep_clean change
  | comp first second one two => simp only [expandTrack, legacyTrack, one, two, Nat.add_zero]
  | inv child ih => exact ih

theorem macro_steps {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    proofSteps (macroTrack change) ≤ 20 := by
  simp only [macroTrack, Stateful.WiringUnion.wireTrack, Cartesian.BoundedOld.steps_map]
  exact Cartesian.BoundedOld.expandStep_steps change

theorem expandPrimitive_steps {a b} {p q : Circuit signature a b} (primitive : Primitive UnionRules p q) :
    proofSteps (expandPrimitive primitive) ≤ 20 := by
  cases rootView primitive with
  | oldWire change => exact macro_steps change
  | crypto | assoc | seqFusion | tensorFusion | cryptoSuffix | wireSuffix | cartesian =>
      change 1 ≤ 20
      omega

theorem expandStep_steps {a b} {p q : Circuit signature a b} (change : Step UnionRules p q) :
    proofSteps (expandStep change) ≤ 20 := by
  induction change with
  | root primitive => exact expandPrimitive_steps primitive
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simpa only [expandStep, Placement.track, Cartesian.BoundedOld.steps_map] using ih

theorem expandTrack_steps {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    proofSteps (expandTrack path) ≤ 20 * proofSteps path := by
  induction path with
  | refl => exact Nat.le_refl 0
  | step change => simpa only [expandTrack, Cartesian.BoundedOld.steps, Nat.mul_one] using expandStep_steps change
  | comp first second one two =>
      simp only [expandTrack, Cartesian.BoundedOld.steps, Nat.mul_add]
      exact Nat.add_le_add one two
  | inv child ih => exact ih

/-- Reuse the exact recorded footprint in the updated full-state model. -/
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
  have rechecked' : Holds updated (fresh (PresentedCell.support proof.cell) changed) := by
    rw [proof.support_eq]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof.cell changed cached' unchanged rechecked' law

/-- info: (0, 20, 1, 0) -/
#guard_msgs in
#eval Id.run do
  let i : Wiring signature finish finish := .identity finish
  let change := oldEdit (Rewrite.Step.root (Rewrite.Root.interchange i i i i))
  let path := Track.step change
  let proof := eliminateTrack path
  return (legacyTrack (expandTrack path), proofSteps (expandTrack path),
    PresentedCell.constructorCount proof.cell, (PresentedCell.support proof.cell).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.OldDefinitions
