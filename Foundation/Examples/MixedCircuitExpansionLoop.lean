import Foundation.Logic.Polygraph.StructuralCartesianExpansionLoopCoherence
import Foundation.Examples.MixedCircuitExpansionCriticalWirePass

/-! The derived expansion/restoration comparison in the existing MAC higher
presentation, including a sampled prefix and an output-discard projection.
No new higher basis, first-level rule or security reduction is introduced. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionLoop
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
open Stateful.WiringUnion
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def comparison {a b c} (p : Wiring signature a b) (q : Wiring signature a c) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.LoopCoherence.expansionCell p q)

theorem comparison_support {a b c} (p : Wiring signature a b) (q : Wiring signature a c) :
    PresentedCell.support (comparison p q) = ∅ := ExpansionCriticalWirePass.pureLift_support _

def loopComparison {a b c} (p : Wiring signature a b) (q : Wiring signature a c) :=
  ExpansionCriticalWirePass.pureLift (ExpansionCritical.LoopCoherence.loopCell p q)

theorem loopComparison_support {a b c} (p : Wiring signature a b) (q : Wiring signature a c) :
    PresentedCell.support (loopComparison p q) = ∅ := ExpansionCriticalWirePass.pureLift_support _

def sampledSource (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage)
    (.wire (Cartesian.fork (Wire.identity MAC.finish) (Wire.identity MAC.finish))))
    (.wire (Cartesian.fst MAC.finish MAC.finish))

def sampledTarget (stage : Nat) :=
  Circuit.seq (Circuit.seq (MAC.before stage)
    (.wire (ExpansionCritical.LoopCoherence.expandedPair (Wire.identity MAC.finish) (Wire.identity MAC.finish))))
    (.wire (Cartesian.fst MAC.finish MAC.finish))

def sampledComparison (stage : Nat) :=
  ((comparison (Wire.identity MAC.finish) (Wire.identity MAC.finish)).whisker (.seqRight (MAC.before stage))).whisker
    (.seqLeft (.wire (Cartesian.fst MAC.finish MAC.finish)))

theorem sampled_support (stage : Nat) : PresentedCell.support (sampledComparison stage) = {stage} := by
  rw [sampledComparison, PresentedCell.whisker_support, PresentedCell.whisker_support, comparison_support]
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

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionLoop
