import Foundation.Logic.Polygraph.StructuralCartesianObservationCoherence
import Foundation.Examples.MixedCircuitTensorNormalizationObstruction
import Foundation.Examples.MixedCircuitLegacyWireRepair

/-! The actual tensor-normalization obligation reduces to atomic output
comparisons. Atom-free output shapes are discharged constructively. The
existing MAC-output obstruction remains visible at one explicit atomic leaf
in the OLD pure basis; no such obstruction for the richer basis is asserted. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.TensorObservation
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def componentThenCanonical {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :=
  Track.comp ((Cartesian.Cell.tensor (Cartesian.normalizeCell p) (Cartesian.normalizeCell q)).toTrack)
    (StatefulWiring.WireFusionResidual.tensorWire p q).toTrack

def direct {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :=
  (Cartesian.normalizeCell (Wire.tensor p q)).toTrack

def tensorComparison {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q)) :
    Cartesian.Higher.Homotopy (componentThenCanonical p q) (direct p q) :=
  ObservationCoherence.reconstruct _ _ certificate

theorem tensor_comparable_iff_atomic {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    Nonempty (Cartesian.Higher.Homotopy (componentThenCanonical p q) (direct p q)) ↔
      Nonempty (ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q)) :=
  ObservationCoherence.comparable_iff_atomic _ _

def terminalTensor {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (left : ObservationCoherence.NoAtoms b) (right : ObservationCoherence.NoAtoms d) :
    Cartesian.Higher.Homotopy (componentThenCanonical p q) (direct p q) :=
  ObservationCoherence.noAtomsCoherent _ _ ⟨left, right⟩

def mixedComparison {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q)) :=
  LegacyCategoryCoherence.pureLift (tensorComparison p q certificate)

theorem mixedComparison_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q)) :
    PresentedCell.support (mixedComparison p q certificate) = ∅ := LegacyCategoryCoherence.pureLift_support _

theorem mixedComparison_definitions {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q)) :
    LegacyWireBasis.definitions (mixedComparison p q certificate) = 0 := LegacyCategoryCoherence.pureLift_definitions _

theorem mixedComparison_context_support {a b c d e f} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q))
    (place : Placement (signature := signature) (.pair a c) (.pair b d) e f) :
    PresentedCell.support ((mixedComparison p q certificate).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, mixedComparison_support, Finset.empty_union]

theorem comparison_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c d e f} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : ObservationCoherence.AtomicCertificate (componentThenCanonical p q) (direct p q))
    (place : Placement (signature := signature) (.pair a c) (.pair b d) e f) (changed : Finset Nat)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value e))) :
    ∃ left : Holds updated (place.apply (.wire (Wire.tensor p q))).needs,
    ∃ right : Holds updated (place.apply (.wire (StatefulWiring.WireFusionResidual.canonical (Wire.tensor p q)))).needs,
      law.bind (fun past => (Stateful.evaluate model.base (place.apply (.wire (Wire.tensor p q)))
        left past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (Stateful.evaluate model.base
        (place.apply (.wire (StatefulWiring.WireFusionResidual.canonical (Wire.tensor p q))))
        right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := (mixedComparison p q certificate).whisker place
  have support : PresentedCell.support proof = place.needs := mixedComparison_context_support p q certificate place
  have cached' : Holds old (PresentedCell.support proof) := by rw [support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof) changed) := by rw [support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof changed cached' unchanged rechecked' law

def obstructedFirst := ProductTracks.firstProjection
  (ProductTracks.firstProjection StatefulWiring.TensorNormalizationObstruction.componentThenCanonical)

def obstructedSecond := ProductTracks.firstProjection
  (ProductTracks.firstProjection StatefulWiring.TensorNormalizationObstruction.direct)

theorem obstructedFirst_weight : @Eq Int (CoherenceInvariant.trackWeight obstructedFirst) 4 := by
  rw [obstructedFirst, ProductTracks.firstProjection, ProductTracks.firstProjection,
    CoherenceInvariant.seqLeft_weight, CoherenceInvariant.seqLeft_weight,
    StatefulWiring.TensorNormalizationObstruction.component_weight]
  rfl

theorem obstructedSecond_weight : @Eq Int (CoherenceInvariant.trackWeight obstructedSecond) 2 := by
  rw [obstructedSecond, ProductTracks.firstProjection, ProductTracks.firstProjection,
    CoherenceInvariant.seqLeft_weight, CoherenceInvariant.seqLeft_weight,
    StatefulWiring.TensorNormalizationObstruction.direct_weight]
  rfl

theorem atomic_obstruction : ¬ Nonempty (Cartesian.Higher.Homotopy obstructedFirst obstructedSecond) := by
  rintro ⟨cell⟩
  have same := CoherenceInvariant.homotopy_weight cell
  rw [obstructedFirst_weight, obstructedSecond_weight] at same
  change (4 : Int) = 2 at same
  omega

theorem original_tensor_still_requires_atomic_diagrams :
    ¬ Nonempty (ObservationCoherence.AtomicCertificate
      StatefulWiring.TensorNormalizationObstruction.componentThenCanonical StatefulWiring.TensorNormalizationObstruction.direct) := by
  rintro ⟨certificate⟩
  exact atomic_obstruction ⟨certificate.1.1⟩

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.TensorObservation
