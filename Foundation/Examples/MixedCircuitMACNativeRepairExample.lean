import Foundation.Examples.MixedCircuitMACNativeContinuationGame

/-! A generated root-association/crypto comparison is lifted through actual
nonempty tensor/copy/discard context, then connected to code-changing native
repair. This is an application of the partial basis, not global coherence. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation.RepairExample
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def fixed (stage : Nat) : Circuit signature (source (stage + 1)) .unit :=
  .seq (before stage) (.wire (.discard finish))

def wrap (stage : Nat) (body : Circuit signature (source (stage + 1)) (.pair finish finish)) :
    Circuit signature (source (stage + 1)) (.pair finish finish) :=
  .seq (.wire (.copy (source (stage + 1))))
    (.seq (.tensor body (fixed stage)) (.wire (.rightUnit (.pair finish finish))))

def originalDiagram (stage : Nat) := wrap stage (.seq (before stage) (.wire (.copy finish)))
def updatedDiagram (stage : Nat) := wrap stage (.seq (after stage) (.wire (.copy finish)))

def localComparison (stage : Nat) :=
  (StatefulWiring.Association.resolve (.box (MACNormalization.Atom.schedule stage))
    (.box (MACNormalization.Atom.eliminate stage)) (.wire (.copy finish))
    (.seqLeft (StatefulWiring.Overlap.crypto stage) (.wire (.copy finish)))).comparison

def comparison (stage : Nat) :=
  (((localComparison stage).whisker (Placement.tensorLeft (fixed stage))).whisker
    (Placement.seqLeft (.wire (.rightUnit (.pair finish finish))))).whisker
    (Placement.seqRight (.wire (.copy (source (stage + 1)))))

theorem comparison_support (stage : Nat) : PresentedCell.support (comparison stage) = {stage, stage + 1} := by
  simp only [comparison, PresentedCell.whisker_support, localComparison, StatefulWiring.Association.resolve_support,
    StatefulWiring.Association.associate_support, Step.support, StatefulWiring.Association.crypto_support,
    Circuit.needs, Placement.needs, fixed, before, StatefulWiring.Association.schedule_needs, StatefulWiring.Association.eliminate_needs,
    Finset.empty_union, Finset.union_empty]
  ext label
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem comparison_count (stage : Nat) : PresentedCell.constructorCount (comparison stage) ≤ 52 := by
  simp only [comparison, PresentedCell.whisker_constructorCount, localComparison]
  exact StatefulWiring.Association.resolveCase_count _

/-- Apply the generic native repair theorem to the GENERATED finite local
comparison, with exact conditions including the branch whose output is dropped. -/
theorem native_repair {State : Type} {old : Nat → Prop} (orders : Nat → Schedule 8) (stage : Nat)
    (changed : Finset Nat) (cached : Holds old {stage, stage + 1})
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh {stage, stage + 1} changed))
    (world : Oracle (Fin 8) (Fin 256) State)
    (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) (source (stage + 1))) :
    ∃ leftValid : Holds (MACNormalization.condition orders) (originalDiagram stage).needs,
    ∃ rightValid : Holds (MACNormalization.condition orders) (updatedDiagram stage).needs,
      ∀ state trace,
        (run .original orders (originalDiagram stage) leftValid world state trace input).map
          (Stateful.stateMap RandomFunctionMACNativeOptimized.relocate) =
        run .optimized orders (updatedDiagram stage) rightValid world state trace input := by
  have cached' : Holds old (PresentedCell.support (comparison stage)) := by rw [comparison_support]; exact cached
  have rechecked' : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support (comparison stage)) changed) := by
    rw [comparison_support]; exact rechecked
  exact repaired_refinement orders (comparison stage) changed cached' unchanged rechecked' world input

theorem charges_retained (stage : Nat) :
    (originalDiagram stage).charges.card = 2 ∧ (updatedDiagram stage).charges.card = 2 := by
  simp [originalDiagram, updatedDiagram, wrap, fixed, before, after, Circuit.charges, signature, MACNormalization.layout]

/-- The selected optimized native prefix retains the full MAC law and bound
when followed by the actual updated mixed diagram. -/
theorem updated_security (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (updatedDiagram stage).needs) (order : Schedule 8) :
    eventProb (((runGame .optimized orders (updatedDiagram stage) valid id).map Prod.fst).map
      RandomFunctionMACNativeCaller.Native.observe) (fun outcome => outcome.result = true) ≤ (256 : ℝ≥0∞)⁻¹ :=
  runGame_security .optimized orders (updatedDiagram stage) valid id order

/-- info: (15, 2, 2, 2) -/
#guard_msgs in
#eval (PresentedCell.constructorCount (comparison 0), (PresentedCell.support (comparison 0)).card,
  (originalDiagram 0).charges.card, (updatedDiagram 0).charges.card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation.RepairExample
