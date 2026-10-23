import Foundation.Logic.Polygraph.StructuralCartesianSubstitutionAssociativityCoherence
import Foundation.Examples.MixedCircuitSubstitutionUnit

/-! Actual substitution associativity in the retained MAC basis. Three
nonlinear/terminal routing layouts are composed in both orders after the same
sampled prefix; guards and the correlated joint law are retained. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.SubstitutionAssociativity
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def comparison {a b c d : Port signature} (f : TypedRouting.Layout a b)
    (g : TypedRouting.Layout b c) (h : TypedRouting.Layout c d) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.SubstitutionAssociativity.forwardCompare f g h)

theorem comparison_support {a b c d : Port signature} (f : TypedRouting.Layout a b)
    (g : TypedRouting.Layout b c) (h : TypedRouting.Layout c d) :
    PresentedCell.support (comparison f g h) = ∅ := ExpansionCriticalWirePass.pureLift_support _

open CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.SubstitutionUnit
  (sampleInput sampleOutput sampleLayout sampledPrefix)

def middleLayout : TypedRouting.Layout sampleOutput sampleInput :=
  (.left (.left (.here _)), .right (.here _))

def sampledSource (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (.seq (.seq (Cartesian.reify sampleLayout) (Cartesian.reify middleLayout)) (Cartesian.reify sampleLayout)))

def sampledTarget (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (Cartesian.reify (Cartesian.substitute sampleLayout (Cartesian.substitute middleLayout sampleLayout))))

def sampledComparison (stage : Nat) :=
  (comparison sampleLayout middleLayout sampleLayout).whisker (.seqRight (sampledPrefix stage))

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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.SubstitutionAssociativity
