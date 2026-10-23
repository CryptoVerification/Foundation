import Foundation.Logic.Polygraph.StructuralCartesianSubstitutionUnitCoherence
import Foundation.Examples.MixedCircuitExpansionCriticalWirePass

/-! The actual public identity-normalization/substitution unit comparison in
the retained MAC basis. A copied sampled pair feeds a nonlinear layout with
an unused input and a terminal output, preserving the original guard. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.SubstitutionUnit
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def comparison {a b : Port signature} (layout : TypedRouting.Layout a b) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.SubstitutionUnit.publicCompare (a := a) (b := b) layout)

theorem comparison_support {a b : Port signature} (layout : TypedRouting.Layout a b) :
    PresentedCell.support (comparison (a := a) (b := b) layout) = ∅ := ExpansionCriticalWirePass.pureLift_support _

def sampleInput : Port signature := .pair MAC.finish MAC.finish
def sampleOutput : Port signature := .pair (.pair MAC.finish .unit) MAC.finish

def sampleLayout : TypedRouting.Layout sampleInput sampleOutput :=
  ((.left (.here _), PUnit.unit), .left (.here _))

def sampledPrefix (stage : Nat) := Circuit.seq (MAC.before stage) (.wire (Wire.copy MAC.finish))

def sampledSource (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (.seq (.identity sampleInput) (Cartesian.reify sampleLayout)))

def sampledTarget (stage : Nat) := Circuit.seq (sampledPrefix stage)
  (.wire (Cartesian.reify (ExpansionCritical.SubstitutionUnit.unitLayout (a := sampleInput) (b := sampleOutput) sampleLayout)))

def sampledComparison (stage : Nat) :=
  (comparison (a := sampleInput) (b := sampleOutput) sampleLayout).whisker (.seqRight (sampledPrefix stage))

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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.SubstitutionUnit
