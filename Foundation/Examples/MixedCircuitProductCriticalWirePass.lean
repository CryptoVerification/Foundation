import Foundation.Crypto.Logic.Polygraph.MixedCircuitCartesianProductCritical
import Foundation.Logic.Polygraph.StructuralCartesianProductCriticalInvariant
import Foundation.Logic.Polygraph.StructuralCartesianProductPeaks
import Foundation.Logic.Polygraph.StructuralCartesianPresentedObservation
import Foundation.Examples.MixedCircuitTensorObservation

/-! Retain the current MAC/legacy library, add explicit product critical
comparisons, and reconstruct comparisons from atomic witnesses in that richer
presentation. Actual canonical tensor coherence remains an atomic obligation.
The previous concrete tensor obstruction persists in the categorical basis. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ProductCriticalWirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

abbrev ProductBasis := CartesianProductCritical.basis Structural.Fusion.basis
def presentation : HigherBasis PresentedWirePass.UnionRules :=
  (contextualBasis LegacyWireBasis.presentation).sum ProductBasis
abbrev Cell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def lift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : LegacyWireBasis.Cell first second) : Cell first second := (cell.injectLeft ProductBasis).embed

theorem lift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : LegacyWireBasis.Cell first second) : PresentedCell.support (lift cell) = PresentedCell.support cell := by
  rw [lift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

theorem lift_constructorCount {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : LegacyWireBasis.Cell first second) : PresentedCell.constructorCount (lift cell) = PresentedCell.constructorCount cell := by
  rw [lift, PresentedCell.embed_constructorCount, PresentedCell.injectLeft_constructorCount]

def productLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell ProductBasis first second) : Cell first second :=
  (cell.injectRight (contextualBasis LegacyWireBasis.presentation)).embed

theorem productLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell ProductBasis first second) : PresentedCell.support (productLift cell) = PresentedCell.support cell := by
  rw [productLift, PresentedCell.embed_support, PresentedCell.injectRight_support]

def pureLift {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : ProductCritical.Cell first second) := productLift (CartesianProductCritical.embedPure Structural.Fusion.basis cell)

theorem pureLift_support {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : ProductCritical.Cell first second) : PresentedCell.support (pureLift cell) = ∅ := by
  rw [pureLift, productLift_support, CartesianProductCritical.embedPure_support]

def atomicComparison {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product first second) :=
  pureLift (PresentedObservation.reconstruct PresentedObservation.product first second certificate)

theorem atomicComparison_support {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product first second) :
    PresentedCell.support (atomicComparison first second certificate) = ∅ := pureLift_support _

def tensorComparison {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :=
  atomicComparison _ _ certificate

theorem tensorComparison_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :
    PresentedCell.support (tensorComparison p q certificate) = ∅ := atomicComparison_support _ _ _

def contract : WirePass.PresentedResidual.Contract PresentedWirePass.sourceRules Structural.Fusion.rules presentation where
  exchange := {
    single := fun generator => lift (LegacyWireRepair.contract.exchange.single generator)
    single_support := fun generator => (lift_support _).trans (LegacyWireRepair.contract.exchange.single_support generator) }
  embed := LegacyWireRepair.contract.embed
  residual := LegacyWireRepair.contract.residual
  square := fun label => lift (LegacyWireRepair.contract.square label)
  embed_support := LegacyWireRepair.contract.embed_support
  residual_covered := LegacyWireRepair.contract.residual_covered
  square_support := fun label => (lift_support _).trans (LegacyWireRepair.contract.square_support label)

def comparison {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q) :=
  WirePass.PresentedResidual.exactTrackSquare contract path

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (PresentedWirePass.framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  exact (LegacyWireRepair.framedComparison stage p q).property.symm.trans (LegacyWireRepair.framed_support stage p q)

def resolvedPeak {a b} {p q r : Wiring signature a b} (peak : ProductCritical.Peak p q r) :=
  pureLift (ProductCritical.resolve peak).cell

theorem resolvedPeak_support {a b} {p q r : Wiring signature a b} (peak : ProductCritical.Peak p q r) :
    PresentedCell.support (resolvedPeak peak) = ∅ := pureLift_support _

theorem atomicComparison_context_support {a b c d} {p q : Wiring signature a b}
    (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product first second)
    (place : Placement (signature := signature) a b c d) :
    PresentedCell.support ((atomicComparison first second certificate).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, atomicComparison_support, Finset.empty_union]

theorem atomicComparison_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c d} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate PresentedObservation.product first second)
    (place : Placement (signature := signature) a b c d) (changed : Finset Nat)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value c))) :
    ∃ left : Holds updated (place.apply (.wire p)).needs,
    ∃ right : Holds updated (place.apply (.wire q)).needs,
      law.bind (fun past => (Stateful.evaluate model.base (place.apply (.wire p))
        left past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (Stateful.evaluate model.base (place.apply (.wire q))
        right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := (atomicComparison first second certificate).whisker place
  have support : PresentedCell.support proof = place.needs := atomicComparison_context_support first second certificate place
  have cached' : Holds old (PresentedCell.support proof) := by rw [support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support proof) changed) := by rw [support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) proof changed cached' unchanged rechecked' law

def samplePair : Wiring signature MAC.finish (.pair MAC.finish MAC.finish) :=
  Cartesian.fork (.identity MAC.finish) (.identity MAC.finish)

def sampleExpanded : Wiring signature MAC.finish (.pair MAC.finish MAC.finish) :=
  Cartesian.fork (.seq samplePair (Cartesian.fst MAC.finish MAC.finish))
    (.seq samplePair (Cartesian.snd MAC.finish MAC.finish))

def sampledSource (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage) (.wire sampleExpanded)) (.wire (Cartesian.fst MAC.finish MAC.finish))

def sampledTarget (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage) (.wire samplePair)) (.wire (Cartesian.fst MAC.finish MAC.finish))

/-- Actual use of the derived fork triangle after one shared MAC computation,
followed by discarding one sampled-output copy through the fst wiring. -/
def sampledComparison (stage : Nat) :=
  ((pureLift (ProductCritical.forkCell (Wire.identity MAC.finish) (Wire.identity MAC.finish))).whisker
    (.seqRight (MAC.before stage))).whisker (.seqLeft (.wire (Cartesian.fst MAC.finish MAC.finish)))

theorem sampled_support (stage : Nat) : PresentedCell.support (sampledComparison stage) = {stage} := by
  rw [sampledComparison, PresentedCell.whisker_support, PresentedCell.whisker_support, pureLift_support]
  simp only [Placement.needs, Circuit.needs, MAC.before, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout,
    Finset.empty_union, Finset.union_empty]

theorem sampled_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    (stage : Nat) (changed : Finset Nat) (cached : Holds old {stage})
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh {stage} changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value (MAC.source (stage + 1))))) :
    ∃ left : Holds updated (sampledSource stage).needs,
    ∃ right : Holds updated (sampledTarget stage).needs,
      law.bind (fun past => (Stateful.evaluate model.base (sampledSource stage)
        left past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (Stateful.evaluate model.base (sampledTarget stage)
        right past.2.1 past.2.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (sampledComparison stage)) := by rw [sampled_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (sampledComparison stage)) changed) := by
    rw [sampled_support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) (sampledComparison stage)
    changed cached' unchanged rechecked' law

theorem actual_atomic_first_weight : @Eq Int
    (ProductCritical.Invariant.trackWeight TensorObservation.obstructedFirst) (-4) := by rfl

theorem actual_atomic_second_weight : @Eq Int
    (ProductCritical.Invariant.trackWeight TensorObservation.obstructedSecond) (-2) := by rfl

theorem actual_atomic_categorical_obstruction :
    ¬ Nonempty (CategoryCritical.Cell TensorObservation.obstructedFirst TensorObservation.obstructedSecond) := by
  rintro ⟨cell⟩
  have same := ProductCritical.Invariant.homotopy_weight cell
  rw [actual_atomic_first_weight, actual_atomic_second_weight] at same
  change (-4 : Int) = -2 at same
  omega

theorem actual_tensor_categorical_obstruction :
    ¬ Nonempty (CategoryCritical.Cell StatefulWiring.TensorNormalizationObstruction.componentThenCanonical
      StatefulWiring.TensorNormalizationObstruction.direct) := by
  rintro ⟨cell⟩
  exact actual_atomic_categorical_obstruction ⟨CategoryCritical.whisker (.seqLeft (Cartesian.fst MAC.finish MAC.finish))
    (CategoryCritical.whisker (.seqLeft (Cartesian.fst (.pair MAC.finish MAC.finish) MAC.finish)) cell)⟩

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ProductCriticalWirePass
