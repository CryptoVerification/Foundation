import Foundation.Crypto.Logic.Polygraph.MixedCircuitCartesianExpansionCritical
import Foundation.Logic.Polygraph.StructuralCartesianExpansionAnnotation
import Foundation.Examples.MixedCircuitDistributionCriticalWirePass

/-! Retain the complete preceding MAC higher library and add four bounded
local expansion comparisons. A sampled tensor/projection overlap is checked
with its exact singleton condition and correlated joint law. Canonical tensor
normalization remains a separate proof obligation. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionCriticalWirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

abbrev ExpansionBasis := CartesianExpansionCritical.basis Structural.Fusion.basis
def presentation : HigherBasis PresentedWirePass.UnionRules :=
  (contextualBasis DistributionCriticalWirePass.presentation).sum ExpansionBasis
abbrev Cell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q) :=
  PresentedCell (contextualBasis presentation) first second

def lift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : DistributionCriticalWirePass.Cell first second) : Cell first second := (cell.injectLeft ExpansionBasis).embed

theorem lift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : DistributionCriticalWirePass.Cell first second) : PresentedCell.support (lift cell) = PresentedCell.support cell := by
  rw [lift, PresentedCell.embed_support, PresentedCell.injectLeft_support]

theorem lift_constructorCount {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : DistributionCriticalWirePass.Cell first second) : PresentedCell.constructorCount (lift cell) = PresentedCell.constructorCount cell := by
  rw [lift, PresentedCell.embed_constructorCount, PresentedCell.injectLeft_constructorCount]

def expansionLift {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell ExpansionBasis first second) : Cell first second :=
  (cell.injectRight (contextualBasis DistributionCriticalWirePass.presentation)).embed

theorem expansionLift_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := PresentedWirePass.UnionRules) p q}
    (cell : PresentedCell ExpansionBasis first second) : PresentedCell.support (expansionLift cell) = PresentedCell.support cell := by
  rw [expansionLift, PresentedCell.embed_support, PresentedCell.injectRight_support]

def pureLift {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : ExpansionCritical.Cell first second) := expansionLift (CartesianExpansionCritical.embedPure Structural.Fusion.basis cell)

theorem pureLift_support {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : ExpansionCritical.Cell first second) : PresentedCell.support (pureLift cell) = ∅ := by
  rw [pureLift, expansionLift_support, CartesianExpansionCritical.embedPure_support]

def atomicComparison {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension first second) :=
  pureLift (PresentedObservation.reconstruct ExpansionCritical.extension first second certificate)

theorem atomicComparison_support {a b} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension first second) :
    PresentedCell.support (atomicComparison first second certificate) = ∅ := pureLift_support _

def tensorComparison {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :=
  atomicComparison _ _ certificate

theorem tensorComparison_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension
      (TensorObservation.componentThenCanonical p q) (TensorObservation.direct p q)) :
    PresentedCell.support (tensorComparison p q certificate) = ∅ := atomicComparison_support _ _ _

def contract : WirePass.PresentedResidual.Contract PresentedWirePass.sourceRules Structural.Fusion.rules presentation where
  exchange := {
    single := fun generator => lift (DistributionCriticalWirePass.contract.exchange.single generator)
    single_support := fun generator => (lift_support _).trans (DistributionCriticalWirePass.contract.exchange.single_support generator) }
  embed := DistributionCriticalWirePass.contract.embed
  residual := DistributionCriticalWirePass.contract.residual
  square := fun label => lift (DistributionCriticalWirePass.contract.square label)
  embed_support := DistributionCriticalWirePass.contract.embed_support
  residual_covered := DistributionCriticalWirePass.contract.residual_covered
  square_support := fun label => (lift_support _).trans (DistributionCriticalWirePass.contract.square_support label)

def comparison {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := PresentedWirePass.sourceRules) p q) :=
  WirePass.PresentedResidual.exactTrackSquare contract path

def framedComparison (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :=
  comparison (PresentedWirePass.framedPath stage p q)

theorem framed_support (stage : Nat) {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (framedComparison stage p q).val = {stage, stage + 1} := by
  rw [(framedComparison stage p q).property]
  exact (DistributionCriticalWirePass.framedComparison stage p q).property.symm.trans (DistributionCriticalWirePass.framed_support stage p q)

theorem atomicComparison_context_support {a b c d} {p q : Wiring signature a b}
    (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension first second)
    (place : Placement (signature := signature) a b c d) :
    PresentedCell.support ((atomicComparison first second certificate).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, atomicComparison_support, Finset.empty_union]

theorem atomicComparison_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c d} {p q : Wiring signature a b} (first second : Cartesian.ProofTrack p q)
    (certificate : PresentedObservation.AtomicCertificate ExpansionCritical.extension first second)
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

def sampledSource (stage : Nat) := Circuit.seq (MAC.before stage)
  (.wire (.seq (Cartesian.fork (Wire.identity MAC.finish) (Wire.identity MAC.finish)) (Cartesian.fst MAC.finish MAC.finish)))

def sampledTarget (stage : Nat) := Circuit.seq (MAC.before stage) (.wire (Wire.identity MAC.finish))

def sampledComparison (stage : Nat) :=
  (pureLift (ExpansionCritical.fstCell (Wire.identity MAC.finish) (Wire.identity MAC.finish))).whisker
    (.seqRight (MAC.before stage))

theorem sampled_support (stage : Nat) : PresentedCell.support (sampledComparison stage) = {stage} := by
  rw [sampledComparison, PresentedCell.whisker_support, pureLift_support]
  simp only [Placement.needs, Circuit.needs, MAC.before, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout,
    Finset.empty_union]

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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionCriticalWirePass
