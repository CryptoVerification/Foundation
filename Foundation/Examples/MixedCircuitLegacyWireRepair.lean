import Foundation.Examples.MixedCircuitLegacyCategoryCoherence

/-! Existing MAC normalization contracts and the root-only legacy expansion
coexist in one presentation. Endpoint wire normalization can follow the
expanded route without extra guards; this is not normalization compatibility
for every root of the full target catalogue. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyWireRepair
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Stateful.WiringUnion
open WirePass
open LegacyWireBasis
set_option backward.isDefEq.respectTransparency false

def contract : PresentedResidual.Contract PresentedWirePass.sourceRules Structural.Fusion.rules presentation where
  exchange := {
    single := fun generator => currentLift (CategoryWirePass.contract.exchange.single generator)
    single_support := fun generator => (currentLift_support _).trans (CategoryWirePass.contract.exchange.single_support generator) }
  embed := CategoryWirePass.contract.embed
  residual := CategoryWirePass.contract.residual
  square := fun label => currentLift (CategoryWirePass.contract.square label)
  embed_support := CategoryWirePass.contract.embed_support
  residual_covered := CategoryWirePass.contract.residual_covered
  square_support := fun label => (currentLift_support _).trans (CategoryWirePass.contract.square_support label)

def comparison {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q) :=
  PresentedResidual.exactTrackSquare contract path

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (PresentedWirePass.framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  exact (CategoryWirePass.framedComparison stage p q).property.symm.trans (CategoryWirePass.framed_support stage p q)

def endpointPass {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := UnionRules) p q) :
    { cell : Cell (.comp path (witness (original := Structural.Fusion.rules) q))
        (.comp (StatefulWiring.OldDefinitions.expandTrack path) (witness (original := Structural.Fusion.rules) q)) //
      PresentedCell.support cell = path.support } := by
  refine ⟨Four.comp (eliminate path).val (.refl (witness (original := Structural.Fusion.rules) q)), ?_⟩
  simp only [PresentedCell.support, (eliminate path).property, witness_support]
  exact Finset.union_eq_left.mpr path.boundaries.2

theorem elimination_repaired_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := UnionRules) p q) (changed : Finset Nat)
    (cached : Holds old path.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh path.support changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : Holds updated p.needs, ∃ right : Holds updated q.needs,
      law.bind (fun past => (Stateful.evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base q right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := eliminate path
  have cached' : Holds old (PresentedCell.support proof.val) := by rw [proof.property]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof.val) changed) := by rw [proof.property]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof.val changed cached' unchanged rechecked' law

theorem endpoint_repaired_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := UnionRules) p q) (changed : Finset Nat)
    (cached : Holds old path.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh path.support changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : Holds updated p.needs, ∃ right : Holds updated (output q).needs,
      law.bind (fun past => (Stateful.evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (output q) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := endpointPass path
  have cached' : Holds old (PresentedCell.support proof.val) := by rw [proof.property]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof.val) changed) := by rw [proof.property]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof.val changed cached' unchanged rechecked' law

theorem mixedComposition_context_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {E : Port signature → Port signature → Type}
    (interpret : ∀ {a b}, E a b → Wiring signature a b) {a b c d}
    {p q : Composition.Expr E a b} (first second : Composition.Finite.Three p q)
    (place : Placement (signature := signature) a b c d) (changed : Finset Nat)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value c))) :
    ∃ left : Holds updated (place.apply (.wire (Cartesian.Higher.CategoryCritical.CompositionTransport.evaluate interpret p))).needs,
    ∃ right : Holds updated (place.apply (.wire (Cartesian.Higher.CategoryCritical.CompositionTransport.evaluate interpret q))).needs,
      law.bind (fun past => (Stateful.evaluate model.base
        (place.apply (.wire (Cartesian.Higher.CategoryCritical.CompositionTransport.evaluate interpret p))) left past.2.1 past.2.2).map
          (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base
          (place.apply (.wire (Cartesian.Higher.CategoryCritical.CompositionTransport.evaluate interpret q))) right past.2.1 past.2.2).map
            (fun next => (past, next))) := by
  let proof := (LegacyCategoryCoherence.mixedCoherence interpret first second).whisker place
  have support : PresentedCell.support proof = place.needs := by
    rw [PresentedCell.whisker_support, LegacyCategoryCoherence.mixedCoherence_support, Finset.empty_union]
  have cached' : Holds old (PresentedCell.support proof) := by rw [support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof) changed) := by rw [support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof changed cached' unchanged rechecked' law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LegacyWireRepair
