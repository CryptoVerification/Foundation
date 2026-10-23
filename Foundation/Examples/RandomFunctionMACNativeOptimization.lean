import Foundation.Constructions.Symmetric.RandomFunctionMACNativeOptimizedRefinement
import Foundation.Examples.GameProofMACNativeQuantitative
import Foundation.Crypto.Logic.General.ResourceImprovement
import Foundation.Crypto.Logic.General.QuantitativeObservationTransport

/-! A code-changing certified MAC implementation with a tighter uniform
caller bound. Both implementations target the same resource type and retain
the complete original observation. This is not pointwise elapsed-time or
code-size dominance; oracle-internal work remains external. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimization
open Foundation.Probability CryptoOracle CryptoOracle.Interactive
open CryptoLogic CryptoLogic.General CryptoLogic.General.ResourceImprovement
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
open RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

noncomputable def source := MACNativeQuantitative.rawObject

def Contract (code : CryptoOracle.Interactive.Code) (horizon : Nat) : Prop :=
  code = RandomFunctionMACNativeOptimized.code ∧ horizon = 286 ∧
  ∀ key : Fin 8 → Fin 256,
    Reification.HaltsWithin code (packetOracle RandomOracle.Cube.coordinateOracle)
      (MACNativeQuantitative.initial key) horizon ∧
    ∀ final ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle RandomOracle.Cube.coordinateOracle)) horizon
      (MACNativeQuantitative.initial key)).support,
      Reification.terminal final.control = true ∧ final.reverseTrace.length = 4

theorem native_contract : Contract RandomFunctionMACNativeOptimized.code 286 := by
  refine ⟨rfl, rfl, fun key => ⟨RandomFunctionMACNativeOptimized.haltsWithin
    RandomOracle.Cube.coordinateOracle (Finset.univ, key) [], ?_⟩⟩
  intro final supported
  simpa only [List.length_nil, Nat.zero_add] using RandomFunctionMACNativeOptimized.whole_halts_queries
    RandomOracle.Cube.coordinateOracle (Finset.univ, key) [] final supported

theorem full_law (order : Schedule 8) :
    (MACNativeQuantitative.run RandomFunctionMACNativeOptimized.code 286).map Native.observe =
      CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw order := by
  unfold MACNativeQuantitative.run CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw
  simp_rw [RandomFunctionMACSchedules.scheduled_state, RandomOracle.Cube.query_eq, Finset.empty_union]
  rw [PMF.map_bind]
  apply congrArg (fun continuation => (uniform (Fin 8 → Fin 256)).bind continuation)
  funext key
  simpa only [MACNativeQuantitative.initial, target_eq_checked] using
    RandomFunctionMACNativeOptimized.observation_law RandomOracle.Cube.coordinateOracle (Finset.univ, key)

noncomputable def common : General.SecurityObject.{0, 0} General.Backends.system .interactive where
  goal := MACNativeQuantitative.rawGoal
  execution := {
    Resources := Nat
    ExecutesWithin := fun _ code horizon => MACNativeQuantitative.ExecutionContract code horizon ∨ Contract code horizon
    Realizes := fun _ _ => MACNativeQuantitative.NativeRealizes }
  adversaries := ⟨fun _ _ => True⟩
  represented := by
    intro F A admissible
    exact ⟨Native.code, 343, Or.inl MACNativeQuantitative.caller_contract, MACNativeQuantitative.native_full_law⟩

def semantic : AdversaryTransform source.goal common.goal := ⟨fun input => input, fun _ observer => observer⟩

noncomputable def original : Implementation source common semantic where
  compiler := .identity (K := General.Backends.system) General.Backends.Kind.interactive
  mapWitness := fun _ _ witness =>
    ⟨witness.code, witness.resources, Or.inl witness.executes, witness.realizes, True.intro⟩
  code_eq := by intros; rfl

noncomputable def optimized : Implementation source common semantic where
  compiler := .primitive (.interactive (.constant RandomFunctionMACNativeOptimized.code))
  mapWitness := fun _ _ _ => ⟨RandomFunctionMACNativeOptimized.code, (286 : Nat), Or.inr native_contract, full_law, True.intro⟩
  code_eq := by intros; rfl

@[instance_reducible]
def resourceOrder : PartialOrder common.execution.Resources := inferInstanceAs (PartialOrder Nat)
attribute [local instance] resourceOrder

theorem improves : Implementation.Improves optimized original := by
  intro F A witness
  change (286 : Nat) ≤ witness.resources
  rw [witness.executes.2.1]
  decide

theorem strictly_smaller_bound (F A) (witness : source.Witness F A) :
    (optimized.mapWitness F A witness).resources < (original.mapWitness F A witness).resources := by
  change (286 : Nat) < witness.resources
  rw [witness.executes.2.1]
  decide

theorem emitted_code (code : CryptoOracle.Interactive.Code) :
    optimized.compiler.run code = RandomFunctionMACNativeOptimized.code := rfl

theorem changed_code (F A) (witness : source.Witness F A) :
    optimized.compiler.run witness.code ≠ original.compiler.run witness.code := by
  change RandomFunctionMACNativeOptimized.code ≠ witness.code
  rw [witness.executes.1]
  exact RandomFunctionMACNativeOptimized.code_changed

noncomputable def observed (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex) :=
  CryptoLogic.Polygraph.Experiment.observe common (MACNativeQuantitative.observation orders vertex)

noncomputable def reduction (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex) :
    General.QuantitativeReduction (MACNativeQuantitative.object orders vertex) (observed orders vertex) :=
  General.QuantitativeReduction.transport optimized.certified
    (MACNativeQuantitative.observation orders vertex) (MACNativeQuantitative.observation orders vertex)
    AdvantageBound.id (by intros; exact le_rfl)

theorem reduction_code (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex)
    (code : CryptoOracle.Interactive.Code) :
    (reduction orders vertex).compiler.run code = RandomFunctionMACNativeOptimized.code := rfl

theorem reduction_resources (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex)
    (F A) (witness : (MACNativeQuantitative.object orders vertex).Witness F A) :
    ((reduction orders vertex).mapWitness F A witness).resources = (286 : Nat) := rfl


namespace Diagnostics

def replies (_ : Unit) (_ : List Bool) : Unit × List Bool := ((), encodeTag (0 : Tag))
noncomputable def constantWorld : Oracle Message Tag Unit := fun _ _ => PMF.pure ((), 0)
def start : Configuration Unit := ⟨(), .running {}, []⟩

theorem constant_packet : packetOracle constantWorld = fun state request => PMF.pure (replies state request) := by
  funext state request
  simp only [packetOracle, constantWorld, replies, PMF.pure_map]

theorem optimized_not_285 :
    ¬ Reification.HaltsWithin RandomFunctionMACNativeOptimized.code (packetOracle constantWorld) start 285 := by
  intro halted
  have supported := Reification.simulate_mem_support RandomFunctionMACNativeOptimized.code replies false 285 start
  have supported' : (Reification.simulate RandomFunctionMACNativeOptimized.code replies false 285 start).1 ∈
      (Reification.eval RandomFunctionMACNativeOptimized.code (packetOracle constantWorld) 285 start).support := by
    rw [constant_packet]; exact supported
  have active : Reification.terminal
      (Reification.simulate RandomFunctionMACNativeOptimized.code replies false 285 start).1.control = false := by decide_cbv
  have impossible := halted _ supported'
  rw [active] at impossible
  contradiction

theorem original_not_342 : ¬ Reification.HaltsWithin Native.code (packetOracle constantWorld) start 342 := by
  intro halted
  have supported := Reification.simulate_mem_support Native.code replies true 342 start
  have supported' : (Reification.simulate Native.code replies true 342 start).1 ∈
      (Reification.eval Native.code (packetOracle constantWorld) 342 start).support := by
    rw [constant_packet]; exact supported
  have active : Reification.terminal (Reification.simulate Native.code replies true 342 start).1.control = false := by decide_cbv
  have impossible := halted _ supported'
  rw [active] at impossible
  contradiction

/-- info: ((285, 343), (286, 286), (251, 252), 4, 4) -/
#guard_msgs in
#eval (((Reification.simulate Native.code replies false 400 start).2,
    (Reification.simulate Native.code replies true 400 start).2),
  ((Reification.simulate RandomFunctionMACNativeOptimized.code replies false 400 start).2,
    (Reification.simulate RandomFunctionMACNativeOptimized.code replies true 400 start).2),
  (Native.code.length, RandomFunctionMACNativeOptimized.code.length),
  ((Reification.simulate Native.code replies true 400 start).1.reverseTrace.length,
    (Reification.simulate RandomFunctionMACNativeOptimized.code replies true 400 start).1.reverseTrace.length))

end Diagnostics

end Foundation.Symmetric.RandomFunctionMACNativeOptimization
