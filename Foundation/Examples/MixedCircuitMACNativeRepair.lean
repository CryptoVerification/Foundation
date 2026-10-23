import Foundation.Examples.MixedCircuitMACNativeContinuation
import Foundation.Examples.MixedCircuitUnifiedAssociationContracts

/-! Connect an explicitly supplied comparison in ANY higher basis of the
actual unified MAC rules to both concrete native implementations. Repair is
inside the updated analysis model; the real physical prefix changes code.
No completeness, native compilation of analysis boxes, or total-cost claim. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Exact footprint repair plus actual emitted-code replacement, keeping the
complete physical frame and sampled mixed output together. -/
theorem repaired_refinement {State : Type} {old : Nat → Prop} (orders : Nat → Schedule 8)
    {basis : HigherBasis StatefulWiring.UnionRules} {n m} {left right : Circuit signature n m}
    {first second : RewriteTrack (relators := StatefulWiring.UnionRules) left right}
    (cell : PresentedCell basis first second) (changed : Finset Nat)
    (cached : Holds old (PresentedCell.support cell))
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support cell) changed))
    (world : Oracle (Fin 8) (Fin 256) State) (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n) :
    ∃ leftValid : Holds (MACNormalization.condition orders) left.needs,
    ∃ rightValid : Holds (MACNormalization.condition orders) right.needs,
      ∀ state trace,
      (run .original orders left leftValid world state trace input).map
        (Stateful.stateMap RandomFunctionMACNativeOptimized.relocate) =
      run .optimized orders right rightValid world state trace input := by
  obtain ⟨_, _, leftValid, rightValid, equal⟩ :=
    Stateful.cell_repaired (StatefulWiring.original orders) cell changed cached unchanged rechecked
  refine ⟨leftValid, rightValid, ?_⟩
  intro state trace
  apply (run_refinement orders left leftValid world state trace input).trans
  unfold run
  apply congrArg (fun continuation => (frames .optimized world state trace).bind continuation)
  funext frame
  exact equal frame (input (RandomFunctionMACNativeCaller.Native.observe frame))

/-- The original correlated history, including initial oracle state and
transcript, is preserved while the native code and the proof diagram change. -/
theorem repaired_refinement_joint {State Context : Type} {old : Nat → Prop} (orders : Nat → Schedule 8)
    {basis : HigherBasis StatefulWiring.UnionRules} {n m} {left right : Circuit signature n m}
    {first second : RewriteTrack (relators := StatefulWiring.UnionRules) left right}
    (cell : PresentedCell basis first second) (changed : Finset Nat)
    (cached : Holds old (PresentedCell.support cell))
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support cell) changed))
    (world : Oracle (Fin 8) (Fin 256) State) (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n)
    (law : PMF (Context × (State × List (List Bool × List Bool)))) :
    ∃ leftValid : Holds (MACNormalization.condition orders) left.needs,
    ∃ rightValid : Holds (MACNormalization.condition orders) right.needs,
      law.bind (fun past => (run .original orders left leftValid world past.2.1 past.2.2 input).map
        (fun result => (past, Stateful.stateMap RandomFunctionMACNativeOptimized.relocate result))) =
      law.bind (fun past => (run .optimized orders right rightValid world past.2.1 past.2.2 input).map
        (fun result => (past, result))) := by
  obtain ⟨leftValid, rightValid, equal⟩ :=
    repaired_refinement orders cell changed cached unchanged rechecked world input
  refine ⟨leftValid, rightValid, ?_⟩
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  have same := congrArg (PMF.map (fun result => (past, result))) (equal past.2.1 past.2.2)
  simpa only [PMF.map_comp, Function.comp_def] using same

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
