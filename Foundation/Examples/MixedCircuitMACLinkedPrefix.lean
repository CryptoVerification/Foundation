import Foundation.Examples.MixedCircuitMACAnalysisNative
import Foundation.Crypto.Semantics.Oracle.NativeVerdictRestore

/-! The optimized actual caller reaches its fourth returned response in
251 transitions, before its comparison suffix. All four adaptive queries
and shared oracle state remain in one execution of the linked code. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
open RandomFunctionMACNativeCaller.Native (returned afterCoin extendTrace)
set_option backward.isDefEq.respectTransparency false

noncomputable def prefixLaw {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) : PMF (Configuration State) :=
  (world state (firstMessage coin)).bind fun first =>
    (world first.1 (secondMessage first.2)).bind fun second =>
      (world second.1 (firstMessage coin)).bind fun repeated =>
        (world repeated.1 7).map fun actual =>
          ⟨actual.1, .running (returned 207 coin (some (if coin then repeated.2 else second.2)) actual.2),
            extendTrace 7 actual.2 (extendTrace (firstMessage coin) repeated.2
              (extendTrace (secondMessage first.2) second.2 (extendTrace (firstMessage coin) first.2 trace)))⟩

theorem after_coin_prefix {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 250
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) = prefixLaw world state trace coin := by
  have duration : 250 = 48 + (48 + ((if coin then 1 else 59) + (48 + ((if coin then 59 else 1) + 46)))) := by
    cases coin <;> decide
  unfold prefixLaw
  rw [duration, TimedExecution.eval_add, first_given_coin_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext first
  rw [TimedExecution.eval_add, second_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext second
  rw [TimedExecution.eval_add, select_second_run, PMF.pure_bind, TimedExecution.eval_add, third_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext repeated
  rw [TimedExecution.eval_add, select_candidate_run, PMF.pure_bind, last_query_run]

theorem prefix_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 251
      (⟨state, .running {}, trace⟩ : Configuration State) = sampleBit.bind (prefixLaw world state trace) := by
  rw [TimedExecution.eval, initial_step, PMF.bind_map]
  change (sampleBit.bind fun coin => TimedExecution.eval (Reification.timedStep code (packetOracle world))
    250 (⟨state, .running (afterCoin coin), trace⟩ : Configuration State)) = _
  simp only [after_coin_prefix]

theorem prefix_active {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (final : Configuration State)
    (supported : final ∈ (sampleBit.bind (prefixLaw world state trace)).support) :
    Reification.terminal final.control = false := by
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨coin, _, supported⟩ := supported
  rw [prefixLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨first, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨second, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨repeated, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  rfl

theorem linked_prefix {State : Type} (tail : Code) (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (HaltReturn.host code tail) (packetOracle world)) 251
      (⟨state, .running {}, trace⟩ : Configuration State) = sampleBit.bind (prefixLaw world state trace) := by
  rw [HaltReturn.active_eval code tail (packetOracle world) 251 _ (by
    intro final supported
    rw [prefix_run] at supported
    exact prefix_active world state trace final supported), prefix_run]

end Foundation.Symmetric.RandomFunctionMACNativeOptimized.AnalysisLinked
