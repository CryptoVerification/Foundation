import Foundation.Examples.RandomFunctionMACNativeOptimization
import Foundation.Crypto.Logic.Polygraph.GameProofTransport
import Foundation.Crypto.Logic.Polygraph.GameProofOrdinaryErasure

/-! Generate implementation-update squares for every serial MAC proof plan.
Only the two atom families (schedule, elimination) are checked locally.
Both routes emit the changed native caller and retain its 286-step packet.
This is not completion of the tensor/copy/discard mixed presentation. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimization.Transported
open Foundation.Probability CryptoLogic CryptoLogic.General
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

noncomputable def schedule (orders : Nat → Schedule 8) (stage : Nat) :
    General.QuantitativeReduction (observed orders (.stage (stage + 1))) (observed orders (.stage stage)) :=
  General.QuantitativeReduction.observe common
    (MACNativeQuantitative.observation orders (.stage (stage + 1)))
    (MACNativeQuantitative.observation orders (.stage stage)) AdvantageBound.id (by
      intro n input observer
      change (CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullGame (orders (stage + 1))).probability ≤
        (CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullGame (orders stage)).probability
      exact (congrArg (fun law : PMF MACNativeQuantitative.FullOutcome => eventProb law (fun out => out.result = true))
        (CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.full_law_eq (orders (stage + 1)) (orders stage))).le)

noncomputable def eliminate (orders : Nat → Schedule 8) (stage : Nat)
    (secure : MACNormalization.condition orders stage) :
    General.QuantitativeReduction (observed orders (.stage stage)) (observed orders .finish) :=
  General.QuantitativeReduction.observe common (MACNativeQuantitative.observation orders (.stage stage))
    (MACNativeQuantitative.observation orders .finish) MACNativeQuantitative.statisticalLoss (by
      intro n input observer
      change (CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullGame (orders stage)).probability ≤
        0 + (256 : ℝ≥0∞)⁻¹
      simpa only [zero_add, MACNormalization.condition] using secure)

theorem schedule_square (orders : Nat → Schedule 8) (stage : Nat) :
    General.QuantitativeComparison
      ((MACNativeQuantitative.schedule orders stage).comp (reduction orders (.stage stage)))
      ((reduction orders (.stage (stage + 1))).comp (schedule orders stage)) := by
  unfold MACNativeQuantitative.schedule reduction schedule
  apply General.QuantitativeReduction.observation_square
  intro n epsilon
  rfl

theorem eliminate_square (orders : Nat → Schedule 8) (stage : Nat) (secure : MACNormalization.condition orders stage) :
    General.QuantitativeComparison
      ((MACNativeQuantitative.eliminate orders stage secure).comp (reduction orders .finish))
      ((reduction orders (.stage stage)).comp (eliminate orders stage secure)) := by
  unfold MACNativeQuantitative.eliminate reduction eliminate
  apply General.QuantitativeReduction.observation_square
  intro n epsilon
  rfl

noncomputable def base (orders : Nat → Schedule 8) :
    Quantitative.Model General.Backends.system (Transport.layout MACNormalization.layout) (MACNormalization.condition orders) where
  machine _ := .interactive
  object := fun
    | .inl vertex => MACNativeQuantitative.object orders vertex
    | .inr vertex => observed orders vertex
  atom label valid := match label with
    | .before original => (MACNativeQuantitative.base orders).atom original valid
    | .after (.schedule stage) => schedule orders stage
    | .after (.eliminate stage) => eliminate orders stage (valid stage (by simp [Transport.layout, MACNormalization.layout]))
    | .bridge vertex => reduction orders vertex

noncomputable def model (orders : Nat → Schedule 8) :
    Quantitative.HigherModel General.Backends.system (Transport.layout MACNormalization.layout)
      (Transport.relators MACNormalization.layout) (MACNormalization.condition orders) where
  base := base orders
  comparison := by
    intro label left right extra
    cases label with
    | schedule stage => exact schedule_square orders stage
    | eliminate stage =>
        exact eliminate_square orders stage (left stage (by
          simp [Transport.relators, Transport.bridge, Plan.needs, Transport.layout, MACNormalization.layout]))

def leftRoute {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :=
  Plan.seq (Transport.before MACNormalization.layout plan) (Transport.bridge MACNormalization.layout b)
def rightRoute {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :=
  Plan.seq (Transport.bridge MACNormalization.layout a) (Transport.after MACNormalization.layout plan)

theorem left_needs {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :
    (leftRoute plan).needs (Transport.layout MACNormalization.layout) = plan.needs MACNormalization.layout := by
  simp only [leftRoute, Plan.needs, Transport.before_needs, Transport.bridge_needs, Finset.union_empty]
theorem right_needs {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :
    (rightRoute plan).needs (Transport.layout MACNormalization.layout) = plan.needs MACNormalization.layout := by
  simp only [rightRoute, Plan.needs, Transport.after_needs, Transport.bridge_needs, Finset.empty_union]

noncomputable def leftReduction (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout)) :=
  Quantitative.evaluate (base orders) (leftRoute plan) (by rw [left_needs]; exact valid)
noncomputable def rightReduction (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout)) :=
  Quantitative.evaluate (base orders) (rightRoute plan) (by rw [right_needs]; exact valid)

theorem comparison (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout)) :
    General.QuantitativeComparison (leftReduction orders plan valid) (rightReduction orders plan valid) := by
  have checked : Holds (MACNormalization.condition orders)
      ((Transport.diagram MACNormalization.layout plan).needs
        (Transport.layout MACNormalization.layout) (Transport.relators MACNormalization.layout)) := by
    rw [Transport.diagram_needs]
    exact valid
  exact Quantitative.evaluateCell (model orders) (Transport.diagram MACNormalization.layout plan) checked

theorem left_code (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (code : CryptoOracle.Interactive.Code) :
    (leftReduction orders plan valid).compiler.run code = RandomFunctionMACNativeOptimized.code := rfl

theorem left_resources (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (F A) (witness : (MACNativeQuantitative.object orders a).Witness F A) :
    ((leftReduction orders plan valid).mapWitness F A witness).resources = (286 : Nat) := rfl

theorem right_code (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (code : CryptoOracle.Interactive.Code) :
    (rightReduction orders plan valid).compiler.run code = RandomFunctionMACNativeOptimized.code :=
  ((comparison orders plan valid).programs code).symm.trans (left_code orders plan valid code)

theorem right_resources (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (F A) (witness : (MACNativeQuantitative.object orders a).Witness F A) :
    ((rightReduction orders plan valid).mapWitness F A witness).resources = (286 : Nat) :=
  ((comparison orders plan valid).resources F A witness).symm.trans (left_resources orders plan valid F A witness)

theorem right_execution (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (F A) (witness : (MACNativeQuantitative.object orders a).Witness F A) :
    Contract ((rightReduction orders plan valid).compiler.run witness.code)
      ((rightReduction orders plan valid).mapWitness F A witness).resources := by
  have executed := (rightReduction orders plan valid).toTransform.compiler_executes F A witness
  change MACNativeQuantitative.ExecutionContract _ _ ∨ Contract _ _ at executed
  rcases executed with earlier | changed
  · have time := earlier.2.1
    change ((rightReduction orders plan valid).mapWitness F A witness).resources = (343 : Nat) at time
    rw [right_resources] at time
    norm_num at time
  · exact changed

theorem right_full_law (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (F A) (witness : (MACNativeQuantitative.object orders a).Witness F A) (order : Schedule 8) :
    (MACNativeQuantitative.run ((rightReduction orders plan valid).compiler.run witness.code)
      ((rightReduction orders plan valid).mapWitness F A witness).resources).map RandomFunctionMACNativeCaller.Native.observe =
      CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw order :=
  (rightReduction orders plan valid).toTransform.compiler_realizes F A witness order

theorem repaired (old updated : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (plan.needs MACNormalization.layout))
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (plan.needs MACNormalization.layout) changed)) :
    let valid := repair cached (fun label outside proof => by
      simpa only [MACNormalization.condition, ← unchanged label outside] using proof) rechecked
    General.QuantitativeComparison (leftReduction updated plan valid) (rightReduction updated plan valid) := by
  exact comparison updated plan _


theorem routes_same_process (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    (plan : Plan MACNormalization.layout a b) (valid : Holds (MACNormalization.condition orders) (plan.needs MACNormalization.layout))
    (code : CryptoOracle.Interactive.Code) {State : Type} (oracle : CryptoOracle.Interactive.BitOracle State)
    (frame : CryptoOracle.Interactive.Configuration State) (horizon : Nat) :
    TimedExecution.eval (CryptoOracle.Interactive.Reification.timedStep
      ((leftReduction orders plan valid).compiler.run code) oracle) horizon frame =
    TimedExecution.eval (CryptoOracle.Interactive.Reification.timedStep
      ((rightReduction orders plan valid).compiler.run code) oracle) horizon frame := by
  rw [(comparison orders plan valid).programs]

/-- Fair ordinary export for this code-changing case: the same local-rule
library yields exactly the same complete rule tree, including its payloads. -/
theorem ordinary_tree {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :
    Foundation.Logic.SharedInference.closedTree
      (CellPresentation.toDerivation (Transport.diagram MACNormalization.layout plan)) =
    CellPresentation.toTree (Transport.diagram MACNormalization.layout plan) :=
  CellPresentation.toDerivation_tree _

theorem ordinary_measure {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b)
    (measure : Foundation.Logic.SharedInference.Tree
      (CellPresentation.Rule (Transport.layout MACNormalization.layout) MACNormalization.Atom) → Nat) :
    measure (Foundation.Logic.SharedInference.closedTree
      (CellPresentation.toDerivation (Transport.diagram MACNormalization.layout plan))) =
    measure (CellPresentation.toTree (Transport.diagram MACNormalization.layout plan)) :=
  congrArg measure (ordinary_tree plan)

theorem ordinary_compilation {a b : MACNormalization.Vertex} (plan : Plan MACNormalization.layout a b) :
    Foundation.Logic.SharedInference.compile
      (T := CellPresentation.theory (Transport.layout MACNormalization.layout) (Transport.relators MACNormalization.layout))
      (Foundation.Logic.SharedInference.closedTree
        (CellPresentation.toDerivation (Transport.diagram MACNormalization.layout plan))) =
    Foundation.Logic.SharedInference.compile
      (T := CellPresentation.theory (Transport.layout MACNormalization.layout) (Transport.relators MACNormalization.layout))
      (CellPresentation.toTree (Transport.diagram MACNormalization.layout plan)) :=
  CellPresentation.toDerivation_compilation _

/-- info: (4, 56, 1, 0) -/
#guard_msgs in
#eval (Transport.generatorCount (Transport.diagram MACNormalization.layout (MACNormalization.strategy.normal (.stage 3))),
  Transport.cellCount (Transport.diagram MACNormalization.layout (MACNormalization.strategy.normal (.stage 3))),
  ((Transport.diagram MACNormalization.layout (MACNormalization.strategy.normal (.stage 3))).needs
    (Transport.layout MACNormalization.layout) (Transport.relators MACNormalization.layout)).card,
  ((Transport.diagram MACNormalization.layout (MACNormalization.strategy.normal (.stage 3))).fresh
    (Transport.layout MACNormalization.layout) (Transport.relators MACNormalization.layout) {1}).card)

-- Both presentations produce accepted certificates with the same complete claim.
/-- info: (true, true, some 56, some 56) -/
#guard_msgs in
#eval Id.run do
  let plan := MACNormalization.strategy.normal (.stage 3)
  let cell := Transport.diagram MACNormalization.layout plan
  let expected : CellPresentation.Claim (Transport.layout MACNormalization.layout) :=
    ⟨Sum.inl (.stage 3), Sum.inr .finish, leftRoute plan, rightRoute plan, plan.needs MACNormalization.layout⟩
  let geometry := CellPresentation.FiniteOrdinary.compileAt (relators := Transport.relators MACNormalization.layout)
    expected (CellPresentation.toTree cell)
  let ordinary := CellPresentation.FiniteOrdinary.compileAt (relators := Transport.relators MACNormalization.layout)
    expected (Foundation.Logic.SharedInference.closedTree (CellPresentation.toDerivation cell))
  return (geometry.isSome, ordinary.isSome, geometry.map (fun proof => proof.data.nodes.length),
    ordinary.map (fun proof => proof.data.nodes.length))

end Foundation.Symmetric.RandomFunctionMACNativeOptimization.Transported
