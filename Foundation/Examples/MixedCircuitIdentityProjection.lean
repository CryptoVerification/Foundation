import Foundation.Logic.Polygraph.StructuralCartesianIdentityProjectionCoherence
import Foundation.Examples.MixedCircuitExpansionCriticalWirePass

/-! Actual product identity normalization/projection squares in the retained
MAC presentation. The sampled context includes MAC.before, full-output copy,
and projection. No replacement normalizer or new basis is introduced. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.IdentityProjection
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def firstComparison (a b : Port signature) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.ProjectionCoherence.normalizeIdentityFst a b)

def secondComparison (a b : Port signature) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.ProjectionCoherence.normalizeIdentitySnd a b)

theorem firstComparison_support (a b : Port signature) : PresentedCell.support (firstComparison a b) = ∅ :=
  ExpansionCriticalWirePass.pureLift_support _

theorem secondComparison_support (a b : Port signature) : PresentedCell.support (secondComparison a b) = ∅ :=
  ExpansionCriticalWirePass.pureLift_support _

def sampledPrefix (stage : Nat) :=
  Circuit.seq (MAC.before stage) (.wire (Wire.copy MAC.finish))

def sampledSource (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (.seq (.identity (.pair MAC.finish MAC.finish)) (Cartesian.fst MAC.finish MAC.finish)))

def sampledTarget (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (ExpansionCritical.ProjectionCoherence.leftCanonical MAC.finish MAC.finish))

def sampledComparison (stage : Nat) :=
  (firstComparison MAC.finish MAC.finish).whisker (.seqRight (sampledPrefix stage))

theorem sampled_support (stage : Nat) : PresentedCell.support (sampledComparison stage) = {stage} := by
  rw [sampledComparison, PresentedCell.whisker_support, firstComparison_support]
  simp only [Placement.needs, sampledPrefix, Circuit.needs, MAC.before, MAC.signature,
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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.IdentityProjection
