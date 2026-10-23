import Foundation.Crypto.Logic.Polygraph.MixedCircuitCartesianDistributionCritical
import Foundation.Logic.Polygraph.StructuralCartesianDistributionAnnotation
import Foundation.Logic.Polygraph.StructuralCartesianDistributionPeaks
import Foundation.Examples.MixedCircuitProductCriticalWirePass

/-! Retain the full previous MAC higher library and add the two local
projection/distribution diagrams and their derived unit triangle. Scalar
annotations certify a remaining canonical tensor obstruction even in the
new pure basis. No complete mixed coherence is inferred. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.DistributionCriticalWirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

abbrev DistributionBasis := CartesianDistributionCritical.basis Structural.Fusion.basis
def presentation : HigherBasis PresentedWirePass.UnionRules :=
  (contextualBasis ProductCriticalWirePass.presentation).sum DistributionBasis
abbrev Cell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def lift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : ProductCriticalWirePass.Cell first second) : Cell first second := (cell.injectLeft DistributionBasis).embed

theorem lift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : ProductCriticalWirePass.Cell first second) : PresentedCell.support (lift cell) = PresentedCell.support cell := by
  rw [lift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

theorem lift_constructorCount {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : ProductCriticalWirePass.Cell first second) : PresentedCell.constructorCount (lift cell) = PresentedCell.constructorCount cell := by
  rw [lift, PresentedCell.embed_constructorCount, PresentedCell.injectLeft_constructorCount]

def productLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell DistributionBasis first second) : Cell first second :=
  (cell.injectRight (contextualBasis ProductCriticalWirePass.presentation)).embed

theorem productLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell DistributionBasis first second) : PresentedCell.support (productLift cell) = PresentedCell.support cell := by
  rw [productLift, PresentedCell.embed_support, PresentedCell.injectRight_support]

def pureLift {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : DistributionCritical.Cell first second) := productLift (CartesianDistributionCritical.embedPure Structural.Fusion.basis cell)

theorem pureLift_support {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : DistributionCritical.Cell first second) : PresentedCell.support (pureLift cell) = ∅ := by
  rw [pureLift, productLift_support, CartesianDistributionCritical.embedPure_support]

def atomicComparison {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension first second) :=
  pureLift (PresentedObservation.reconstruct DistributionCritical.extension first second certificate)

theorem atomicComparison_support {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension first second) :
    PresentedCell.support (atomicComparison first second certificate) = ∅ := pureLift_support _

def tensorComparison {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :=
  atomicComparison _ _ certificate

theorem tensorComparison_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :
    PresentedCell.support (tensorComparison p q certificate) = ∅ := atomicComparison_support _ _ _

def contract : WirePass.PresentedResidual.Contract PresentedWirePass.sourceRules Structural.Fusion.rules presentation where
  exchange := {
    single := fun generator => lift (ProductCriticalWirePass.contract.exchange.single generator)
    single_support := fun generator => (lift_support _).trans (ProductCriticalWirePass.contract.exchange.single_support generator) }
  embed := ProductCriticalWirePass.contract.embed
  residual := ProductCriticalWirePass.contract.residual
  square := fun label => lift (ProductCriticalWirePass.contract.square label)
  embed_support := ProductCriticalWirePass.contract.embed_support
  residual_covered := ProductCriticalWirePass.contract.residual_covered
  square_support := fun label => (lift_support _).trans (ProductCriticalWirePass.contract.square_support label)

def comparison {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q) :=
  WirePass.PresentedResidual.exactTrackSquare contract path

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (PresentedWirePass.framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  exact (ProductCriticalWirePass.framedComparison stage p q).property.symm.trans (ProductCriticalWirePass.framed_support stage p q)

def resolvedPeak {a b} {p q r : Wiring signature a b} (peak : DistributionCritical.Peak p q r) :=
  pureLift (DistributionCritical.resolve peak).cell

theorem resolvedPeak_support {a b} {p q r : Wiring signature a b} (peak : DistributionCritical.Peak p q r) :
    PresentedCell.support (resolvedPeak peak) = ∅ := pureLift_support _

theorem atomicComparison_context_support {a b c d} {p q : Wiring signature a b}
    (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension first second)
    (place : Placement (signature := signature) a b c d) :
    PresentedCell.support ((atomicComparison first second certificate).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, atomicComparison_support, Finset.empty_union]

theorem atomicComparison_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c d} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate DistributionCritical.extension first second)
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

def sampleExpanded : Wiring signature MAC.finish (.pair MAC.finish MAC.finish) := .seq (.identity MAC.finish) samplePair

def sampledSource (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage) (.wire sampleExpanded)) (.wire (Cartesian.fst MAC.finish MAC.finish))

def sampledTarget (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage) (.wire samplePair)) (.wire (Cartesian.fst MAC.finish MAC.finish))

def sampledComparison (stage : Nat) :=
  ((pureLift (DistributionCritical.identityCell (Wire.identity MAC.finish) (Wire.identity MAC.finish))).whisker
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

def tensorCoeff (index : Fin 18) : Int := if index.val = 8 then 1 else 0

theorem tensorCoeff_admissible : DistributionCritical.Annotation.Admissible tensorCoeff :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem actual_atomic_first_weight : @Eq Int
    (RootAnnotation.trackWeight tensorCoeff TensorObservation.obstructedFirst) 3 := by rfl

theorem actual_atomic_second_weight : @Eq Int
    (RootAnnotation.trackWeight tensorCoeff TensorObservation.obstructedSecond) 1 := by rfl

theorem actual_atomic_distribution_obstruction :
    ¬ Nonempty (DistributionCritical.Cell TensorObservation.obstructedFirst TensorObservation.obstructedSecond) := by
  rintro ⟨cell⟩
  have same := DistributionCritical.Annotation.homotopy_weight tensorCoeff_admissible cell
  rw [actual_atomic_first_weight, actual_atomic_second_weight] at same
  change (3 : Int) = 1 at same
  omega

theorem actual_tensor_distribution_obstruction :
    ¬ Nonempty (DistributionCritical.Cell StatefulWiring.TensorNormalizationObstruction.componentThenCanonical
      StatefulWiring.TensorNormalizationObstruction.direct) := by
  rintro ⟨cell⟩
  exact actual_atomic_distribution_obstruction ⟨DistributionCritical.whisker (.seqLeft (Cartesian.fst MAC.finish MAC.finish))
    (DistributionCritical.whisker (.seqLeft (Cartesian.fst (.pair MAC.finish MAC.finish) MAC.finish)) cell)⟩

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.DistributionCriticalWirePass
