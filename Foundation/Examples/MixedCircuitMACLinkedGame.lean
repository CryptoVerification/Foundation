import Foundation.Examples.MixedCircuitMACLinkedExecution

/-! The compiled analysis is part of a single native execution with a proved
uniform bound. Its original full MAC observation, four requests and protocol
encoding are retained. Key generation and oracle internals remain external. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open CryptoLogic.Polygraph.MixedCircuit
open CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
open Foundation.Logic.Polygraph.ScheduleCertificate
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

theorem observation_law {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State) :
    (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (budget mask)
      (⟨state, .running {}, []⟩ : Configuration State)).map RandomFunctionMACNativeCaller.Native.observe =
      target.run world state := by
  rw [whole_run_original, PMF.map_comp]
  have invariant : (RandomFunctionMACNativeCaller.Native.observe (State := State)) ∘ finalize mask = RandomFunctionMACNativeCaller.Native.observe :=
    funext (observe_finalize mask)
  rw [invariant]
  exact RandomFunctionMACNativeOptimized.observation_law world state

theorem prefix_encoded {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ budget mask) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support) :
    ∀ entry ∈ current.reverseTrace, EncodedPair entry := by
  obtain ⟨final, reachable, included⟩ := Reification.extend_prefix (linkedCode mask) (packetOracle world) fuel (budget mask)
    within ⟨state, .running {}, []⟩ current supported
  rw [whole_run_original, PMF.mem_support_map_iff] at reachable
  obtain ⟨oldFinal, oldSupported, rfl⟩ := reachable
  intro entry member
  have original := RandomFunctionMACNativeOptimized.prefix_encoded world state 286 (Nat.le_refl _) oldFinal oldSupported
  exact original entry (by rw [← trace_finalize mask oldFinal]; exact included member)

theorem awaiting_format {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ budget mask) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support)
    (machine : Machine.Configuration) (request : List Bool) (waiting : current.control = .awaiting machine request) :
    ∃ message : Message, request = encodeMessage message := by
  have before : fuel < budget mask := by
    by_contra outside
    have last : fuel = budget mask := by omega
    subst fuel
    have halted := (whole_halts_queries mask world state [] current supported).1
    simp [waiting, Reification.terminal] at halted
  obtain ⟨answer, reachable⟩ := PMF.support_nonempty (packetOracle world current.state request)
  let next : Configuration State := ⟨answer.1, .loading machine answer.2 {}, (request, answer.2) :: current.reverseTrace⟩
  have stepLaw : Reification.timedStep (linkedCode mask) (packetOracle world) current =
      (packetOracle world current.state request).map (fun response =>
        (⟨response.1, .loading machine response.2 {}, (request, response.2) :: current.reverseTrace⟩ : Configuration State)) := by
    simp [Reification.timedStep, waiting, Reification.terminal, Reification.perform, Reification.action, transition]
  have stepSupported : next ∈ (Reification.timedStep (linkedCode mask) (packetOracle world) current).support := by
    rw [stepLaw, PMF.mem_support_map_iff]
    exact ⟨answer, reachable, rfl⟩
  have nextSupported : next ∈ (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (fuel + 1)
      (⟨state, .running {}, []⟩ : Configuration State)).support := by
    rw [TimedExecution.eval_add, PMF.mem_support_bind_iff]
    refine ⟨current, supported, ?_⟩
    simpa [TimedExecution.eval] using stepSupported
  obtain ⟨message, _tag, same⟩ := prefix_encoded mask world state (fuel + 1) (by omega) next nextSupported
    (request, answer.2) (List.mem_cons_self ..)
  exact ⟨message, congrArg Prod.fst same⟩


def packetView {State : Type} (count : Nat) (frame : Configuration State) : List Bool :=
  match frame.control with | .running machine => NativeVerdictRestore.read count machine.outputTape | _ => []

theorem packet_finalize {State : Type} (mask : List Bool) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) :
    packetView mask.length (finalize mask ⟨state, .running machine, trace⟩) =
      NativeVerdictPacket.result mask (RandomFunctionMACNativeCaller.Native.observe ⟨state, .running machine, trace⟩).result := by
  simp only [packetView, finalize, CodeRelocation.frame, CodeRelocation.control, NativeVerdictRestore.finish,
    Machine.Configuration.rebasePc]
  rw [← NativeVerdictPacket.result_length mask (machine.outputTape.current.getD false), NativeVerdictRestore.read_restored]
  rfl

/-- Both the original full game output and the physically written analysis
bits belong to the same uninterrupted linked run. -/
theorem joint_run {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (budget mask)
      (⟨state, .running {}, trace⟩ : Configuration State)).map
        (fun frame => (RandomFunctionMACNativeCaller.Native.observe frame, packetView mask.length frame)) =
    (TimedExecution.eval (Reification.timedStep RandomFunctionMACNativeOptimized.code (packetOracle world)) 286
      (⟨state, .running {}, trace⟩ : Configuration State)).map
        (fun frame => (RandomFunctionMACNativeCaller.Native.observe frame,
          NativeVerdictPacket.result mask (RandomFunctionMACNativeCaller.Native.observe frame).result)) := by
  rw [whole_run, RandomFunctionMACNativeOptimized.whole_run]
  simp only [executionLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, observe_finalize, packet_finalize]

/-- Relate the real packet jointly with the original full outcome to the
original guarded MAC analysis, rather than validate only a standalone block. -/
theorem compiled_joint (orders : Nat → Schedule 8) {stage : Nat} {m}
    (circuit : Circuit signature (source stage) m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle Message Tag MACNativeQuantitative.State) (state : MACNativeQuantitative.State)
    (trace : List (List Bool × List Bool)) :
    (TimedExecution.eval (Reification.timedStep (linkedCode (AnalysisCompilation.flags circuit)) (packetOracle world))
      (budget (AnalysisCompilation.flags circuit)) (⟨state, .running {}, trace⟩ : Configuration MACNativeQuantitative.State)).map
        (fun frame => (RandomFunctionMACNativeCaller.Native.observe frame, packetView (AnalysisCompilation.width m) frame)) =
    (TimedExecution.eval (Reification.timedStep RandomFunctionMACNativeOptimized.code (packetOracle world)) 286
      (⟨state, .running {}, trace⟩ : Configuration MACNativeQuantitative.State)).bind fun frame =>
        (CryptoLogic.Polygraph.MixedCircuit.evaluate (CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.base orders) circuit valid (RandomFunctionMACNativeCaller.Native.observe frame)).map
          (fun output => (RandomFunctionMACNativeCaller.Native.observe frame, AnalysisCompilation.verdicts orders m output)) := by
  rw [← AnalysisCompilation.flags_length circuit, joint_run]
  simp_rw [AnalysisCompilation.compile_correct, PMF.pure_map, AnalysisCompilation.restored_verdicts]
  rfl


noncomputable def gameRun (mask : List Bool) : PMF (Configuration MACNativeQuantitative.State) :=
  (uniform (Fin 8 → Fin 256)).bind fun key =>
    TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle RandomOracle.Cube.coordinateOracle))
      (budget mask) (MACNativeQuantitative.initial key)

theorem full_law (mask : List Bool) (order : Schedule 8) :
    (gameRun mask).map RandomFunctionMACNativeCaller.Native.observe =
      CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw order := by
  have source := RandomFunctionMACNativeOptimization.full_law order
  unfold gameRun MACNativeQuantitative.run at *
  simp only [PMF.map_bind] at *
  rw [← source]
  apply congrArg (fun continuation => (uniform (Fin 8 → Fin 256)).bind continuation)
  funext key
  change ((TimedExecution.eval _ _ (⟨(Finset.univ, key), .running {}, []⟩ : Configuration MACNativeQuantitative.State)).map _) = _
  rw [observation_law]
  exact (RandomFunctionMACNativeOptimized.observation_law RandomOracle.Cube.coordinateOracle (Finset.univ, key)).symm

theorem security (mask : List Bool) (order : Schedule 8) :
    eventProb ((gameRun mask).map RandomFunctionMACNativeCaller.Native.observe) (fun outcome => outcome.result = true) ≤
      (256 : ℝ≥0∞)⁻¹ := by
  rw [full_law mask order]
  exact CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.full_security order

def compiled {stage : Nat} {m} (circuit : Circuit signature (source stage) m) : Code :=
  linkedCode (AnalysisCompilation.flags circuit)

theorem compiled_length {stage : Nat} {m} (circuit : Circuit signature (source stage) m) :
    (compiled circuit).length = 257 + 5 * AnalysisCompilation.width m := by
  rw [compiled, linkedCode_length, AnalysisCompilation.flags_length]

theorem compiled_budget {stage : Nat} {m} (circuit : Circuit signature (source stage) m) :
    budget (AnalysisCompilation.flags circuit) = 290 + 3 * AnalysisCompilation.width m := by
  rw [budget, AnalysisCompilation.flags_length]; omega

theorem repaired_compiled_eq {old : Nat → Prop} (orders : Nat → Schedule 8)
    {basis : HigherBasis StatefulWiring.UnionRules} {stage : Nat} {m}
    {left right : Circuit signature (source stage) m}
    {first second : RewriteTrack (relators := StatefulWiring.UnionRules) left right}
    (cell : PresentedCell basis first second) (changed : Finset Nat) (cached : Holds old (PresentedCell.support cell))
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support cell) changed)) :
    compiled left = compiled right := by
  -- Recover masks from the proven pure bit semantics rather than assume
  -- injectivity of the native code constructor.
  obtain ⟨_, _, leftValid, rightValid, equal⟩ := Stateful.cell_repaired
    (StatefulWiring.checked (Stateful.liftChecked (State := Unit) (AnalysisCompilation.checkedBits orders))) cell changed cached unchanged rechecked
  have kernels := equal () true
  change Stateful.evaluate (Stateful.lift (AnalysisCompilation.model orders)) left leftValid () true =
    Stateful.evaluate (Stateful.lift (AnalysisCompilation.model orders)) right rightValid () true at kernels
  simp only [Stateful.evaluate_lift, AnalysisCompilation.evaluate_bits, PMF.pure_map] at kernels
  have member : ((), AnalysisCompilation.output left true) ∈ (PMF.pure ((), AnalysisCompilation.output left true)).support := by simp
  rw [kernels] at member
  have outputs := congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp member)
  exact congrArg (fun bits => linkedCode (AnalysisCompilation.flatten m bits)) outputs

theorem haltsWithin {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    Reification.HaltsWithin (linkedCode mask) (packetOracle world) ⟨state, .running {}, trace⟩ (budget mask) := by
  intro final supported
  rw [← Reification.timed_eval_eq] at supported
  exact (whole_halts_queries mask world state trace final supported).1

theorem example_compiled_eq (orders : Nat → Schedule 8) (stage : Nat) :
    compiled (NativeContinuation.RepairExample.originalDiagram stage) = compiled (NativeContinuation.RepairExample.updatedDiagram stage) :=
  repaired_compiled_eq orders (NativeContinuation.RepairExample.comparison stage) ∅
    (MACNormalization.conditions orders _) (fun _ _ proof => proof) (MACNormalization.conditions orders _)

/-- info: (267, 296) -/
#guard_msgs in
#eval ((compiled (NativeContinuation.analysis 0)).length, budget (AnalysisCompilation.flags (NativeContinuation.analysis 0)))

end Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
