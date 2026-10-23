import Foundation.Examples.MixedCircuitMACLinkedPrefix

/-! A single actual linked program: four adaptive native MAC calls, original
comparison, real halt-to-return jump, materialized verdict packet and physical
head restoration. Oracle internals/key sampling remain external services. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
open RandomFunctionMACNativeCaller.Native (returned extendTrace)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def linkedCode (mask : List Bool) : Code := HaltReturn.host RandomFunctionMACNativeOptimized.code (NativeVerdictRestore.code mask)
def budget (mask : List Bool) : Nat := 286 + (3 * mask.length + 4)

def finalize {State : Type} (mask : List Bool) (frame : Configuration State) : Configuration State :=
  match frame.control with
  | .running machine => CodeRelocation.frame RandomFunctionMACNativeOptimized.code.length
      ⟨frame.state, .running (NativeVerdictRestore.finish mask machine.inputTape machine.outputTape), frame.reverseTrace⟩
  | _ => frame

theorem linkedCode_length (mask : List Bool) : (linkedCode mask).length = 257 + 5 * mask.length := by
  rw [linkedCode, HaltReturn.host_length, RandomFunctionMACNativeOptimized.code_length, NativeVerdictRestore.code_length]
  omega

theorem comparison_run {State : Type} (mask : List Bool) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate actual : Tag) :
    TimedExecution.eval (Reification.timedStep (linkedCode mask) oracle) (35 + (3 * mask.length + 4))
      (⟨state, .running (returned 207 coin (some candidate) actual), trace⟩ : Configuration State) =
      PMF.pure (finalize mask ⟨state, .running (comparisonResult coin candidate actual).1, trace⟩) := by
  let ticks := 1 + (comparisonResult coin candidate actual).2
  have prefixRun := NativeDeterministic.finish_return RandomFunctionMACNativeOptimized.code
    (NativeVerdictRestore.code mask) 35 (returned 207 coin (some candidate) actual)
    (comparisonResult coin candidate actual).1 ticks rfl (comparison_full_checked coin candidate actual)
  have prefixLaw := NativeDeterministic.run_sound _ oracle state trace _ _ _ prefixRun
  have bound : ticks ≤ 35 := (comparison_halts coin candidate actual).2
  rw [show 35 + (3 * mask.length + 4) = ticks + ((3 * mask.length + 4) + (35 - ticks)) by omega,
    TimedExecution.eval_add]
  change ((TimedExecution.eval (Reification.timedStep (HaltReturn.host RandomFunctionMACNativeOptimized.code
    (NativeVerdictRestore.code mask)) oracle) ticks _).bind _) = _
  rw [prefixLaw, PMF.pure_bind]
  change TimedExecution.eval (Reification.timedStep (HaltReturn.host RandomFunctionMACNativeOptimized.code
    (NativeVerdictRestore.code mask)) oracle) ((3 * mask.length + 4) + (35 - ticks))
      (CodeRelocation.frame RandomFunctionMACNativeOptimized.code.length
        ⟨state, .running (NativeVerdictPacket.start 0 (comparisonResult coin candidate actual).1.inputTape
          (comparisonResult coin candidate actual).1.outputTape), trace⟩) = _
  rw [HaltReturn.body_eval, TimedExecution.eval_add, NativeVerdictRestore.timed, PMF.pure_bind,
    Reification.timed_eval_eq, Reification.eval_terminal _ _ _ _ rfl, PMF.pure_map]
  rfl

theorem whole_run {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (budget mask)
      (⟨state, .running {}, trace⟩ : Configuration State) =
      (sampleBit.bind (executionLaw world state trace)).map (finalize mask) := by
  rw [show budget mask = 251 + (35 + (3 * mask.length + 4)) by unfold budget; omega, TimedExecution.eval_add]
  change ((TimedExecution.eval (Reification.timedStep (HaltReturn.host RandomFunctionMACNativeOptimized.code
    (NativeVerdictRestore.code mask)) (packetOracle world)) 251 _).bind _) = _
  rw [linked_prefix]
  simp only [prefixLaw, executionLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext coin
  congr 1
  funext first
  congr 1
  funext second
  congr 1
  funext repeated
  rw [PMF.map]
  congr 1
  funext actual
  exact comparison_run mask (packetOracle world) actual.1 _ coin _ actual.2

theorem whole_run_original {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (budget mask)
      (⟨state, .running {}, trace⟩ : Configuration State) =
    (TimedExecution.eval (Reification.timedStep RandomFunctionMACNativeOptimized.code (packetOracle world)) 286
      (⟨state, .running {}, trace⟩ : Configuration State)).map (finalize mask) := by
  rw [whole_run, RandomFunctionMACNativeOptimized.whole_run]

theorem observe_finalize {State : Type} (mask : List Bool) (frame : Configuration State) :
    RandomFunctionMACNativeCaller.Native.observe (finalize mask frame) = RandomFunctionMACNativeCaller.Native.observe frame := by
  cases frame with
  | mk state control trace =>
    cases control <;> simp only [finalize]
    simp only [CodeRelocation.frame, CodeRelocation.control, RandomFunctionMACNativeCaller.Native.observe,
      RandomFunctionMACNativeCaller.Native.verdict, NativeVerdictRestore.finish, NativeVerdictRestore.restored_layout,
      Machine.Configuration.rebasePc]

theorem trace_finalize {State : Type} (mask : List Bool) (frame : Configuration State) :
    (finalize mask frame).reverseTrace = frame.reverseTrace := by cases frame with | mk state control trace => cases control <;> rfl

theorem terminal_finalize {State : Type} (mask : List Bool) (frame : Configuration State)
    (terminal : Reification.terminal frame.control = true) : Reification.terminal (finalize mask frame).control = true := by
  cases frame with | mk state control trace => cases control <;> simp_all [finalize, CodeRelocation.frame, CodeRelocation.control,
    Reification.terminal, NativeVerdictRestore.finish, Machine.Configuration.rebasePc]

theorem whole_halts_queries {State : Type} (mask : List Bool) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (final : Configuration State)
    (supported : final ∈ (TimedExecution.eval (Reification.timedStep (linkedCode mask) (packetOracle world)) (budget mask)
      (⟨state, .running {}, trace⟩ : Configuration State)).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [whole_run_original, PMF.mem_support_map_iff] at supported
  obtain ⟨original, reachable, rfl⟩ := supported
  obtain ⟨terminal, queries⟩ := RandomFunctionMACNativeOptimized.whole_halts_queries world state trace original reachable
  exact ⟨terminal_finalize mask original terminal, by rw [trace_finalize]; exact queries⟩

end Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
