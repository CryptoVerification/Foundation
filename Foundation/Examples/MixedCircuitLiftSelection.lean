import Foundation.Logic.Polygraph.StructuralCartesianLiftSelectionCoherence
import Foundation.Examples.MixedCircuitExpansionCriticalWirePass

/-! Embed actual lift/selection comparisons in the retained MAC basis. The
sample duplicates one sampled full output, creates a repeated three-output
layout, and selects its nested middle output while retaining the MAC guard. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LiftSelection
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

abbrev Side := ExpansionCritical.LiftSelection.Side

def comparison (side : Side) (extra : Port signature) {a b : Port signature} (layout : TypedRouting.Layout a b)
    {name : signature.PortAtom} (slot : TypedRouting.Slot b name) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.LiftSelection.compare side extra (a := a) layout slot)

theorem comparison_support (side : Side) (extra : Port signature) {a b : Port signature} (layout : TypedRouting.Layout a b)
    {name : signature.PortAtom} (slot : TypedRouting.Slot b name) : PresentedCell.support (comparison side extra layout slot) = ∅ :=
  ExpansionCriticalWirePass.pureLift_support _

def sampleShape : Port signature := .pair (.pair MAC.finish MAC.finish) MAC.finish

def sampleLayout : TypedRouting.Layout MAC.finish sampleShape := ((.here _, .here _), .here _)

def sampleSlot : TypedRouting.Slot sampleShape MACNormalization.Vertex.finish := .left (.right (.here _))

def sampledPrefix (stage : Nat) := Circuit.seq (MAC.before stage) (.wire (Wire.copy MAC.finish))

def sampledSource (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (.seq (.seq (Cartesian.fst MAC.finish MAC.finish) (Cartesian.reify sampleLayout)) (Cartesian.reifyRef sampleSlot)))

def sampledTarget (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (Cartesian.reifyRef (TypedRouting.read sampleSlot
    (ExpansionCritical.LiftSelection.mapLayout .left MAC.finish (a := MAC.finish) sampleLayout))))

def sampledComparison (stage : Nat) :=
  (comparison .left MAC.finish (a := MAC.finish) (b := sampleShape) sampleLayout sampleSlot).whisker (.seqRight (sampledPrefix stage))

theorem sampled_support (stage : Nat) : PresentedCell.support (sampledComparison stage) = {stage} := by
  rw [sampledComparison, PresentedCell.whisker_support, comparison_support]
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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.LiftSelection
