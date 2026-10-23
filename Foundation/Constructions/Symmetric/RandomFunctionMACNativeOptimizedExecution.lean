import Foundation.Constructions.Symmetric.RandomFunctionMACNativeOptimized

/-! Whole continuing execution of dead-store optimized MAC caller. The
uniform 286-transition bound includes every native operation and all four
packet transfers. Oracle-internal work remains the same external capability. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
open RandomFunctionMACNativeCaller.Native (memory machineAt returned residue extendTrace afterCoin firstCall)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem first_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (firstCall coin), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 _ _ (first_setup_checked coin)

theorem initial_step {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    Reification.timedStep code oracle (⟨state, .running {}, trace⟩ : Configuration State) =
      sampleBit.map (fun coin => ⟨state, .running (afterCoin coin), trace⟩) := by
  simp only [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, code, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Bool.false_eq_true, if_false]
  congr 1
  funext coin
  cases coin <;> rfl

theorem first_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (firstCall coin), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 16 coin none answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  have location : code[(firstCall coin).pc]? = some .call := by cases coin <;> decide_cbv
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (firstCall coin)
    state trace (encodeMessage (firstMessage coin)) [] [] rfl location rfl 8
    (packet_response_width world state (encodeMessage (firstMessage coin)))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, firstCall, returned, machineAt, memory, extendTrace] using law

theorem first_given_coin_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 16 coin none answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, first_setup_run, PMF.pure_bind, first_transfer]

theorem second_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (returned 16 coin none first), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (secondCall coin first), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 _ _ (second_setup_checked coin first)

theorem third_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (saved : Option Tag) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (returned 106 coin saved second), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (thirdCall coin saved second), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 _ _ (third_setup_checked coin saved second)

theorem last_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 10
      (⟨state, .running (returned 196 coin (some candidate) repeated), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (lastCall coin candidate repeated), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 10 _ _ (last_setup_checked coin candidate repeated)

theorem select_second_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) (if coin then 1 else 59)
      (⟨state, .running (returned 31 coin none second), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (returned 106 coin (savedSecond coin second) second), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace _ _ _ (select_second_checked coin second)

theorem select_candidate_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) (if coin then 59 else 1)
      (⟨state, .running (returned 121 coin (savedSecond coin second) repeated), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (returned 196 coin (some (if coin then repeated else second)) repeated), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace _ _ _ (select_candidate_checked coin second repeated)

theorem second_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (secondCall coin first), trace⟩ : Configuration State) =
      (world state (secondMessage first)).map (fun answer =>
        ⟨answer.1, .running (returned 31 coin none answer.2), extendTrace (secondMessage first) answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (secondCall coin first)
    state trace (encodeMessage (secondMessage first)) [] (residue first) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage (secondMessage first)))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, secondCall,
    RandomFunctionMACNativeCaller.Native.secondCall, returned, machineAt, extendTrace] using law

theorem third_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (saved : Option Tag) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (thirdCall coin saved second), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 121 coin saved answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (thirdCall coin saved second)
    state trace (encodeMessage (firstMessage coin)) [] (residue second) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage (firstMessage coin)))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, thirdCall, returned, machineAt, extendTrace] using law

theorem last_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (lastCall coin candidate repeated), trace⟩ : Configuration State) =
      (world state 7).map (fun answer =>
        ⟨answer.1, .running (returned 207 coin (some candidate) answer.2), extendTrace 7 answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (lastCall coin candidate repeated)
    state trace (encodeMessage 7) [] (residue repeated) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage 7))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, lastCall, returned, machineAt, extendTrace] using law

theorem second_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (returned 16 coin none first), trace⟩ : Configuration State) =
      (world state (secondMessage first)).map (fun answer =>
        ⟨answer.1, .running (returned 31 coin none answer.2), extendTrace (secondMessage first) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, second_setup_run, PMF.pure_bind, second_transfer]

theorem third_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (saved : Option Tag) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (returned 106 coin saved second), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 121 coin saved answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, third_setup_run, PMF.pure_bind, third_transfer]

theorem last_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 46
      (⟨state, .running (returned 196 coin (some candidate) repeated), trace⟩ : Configuration State) =
      (world state 7).map (fun answer =>
        ⟨answer.1, .running (returned 207 coin (some candidate) answer.2), extendTrace 7 answer.2 trace⟩) := by
  rw [show 46 = 10 + 36 by rfl, TimedExecution.eval_add, last_setup_run, PMF.pure_bind, last_transfer]

theorem comparison_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate actual : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 35
      (⟨state, .running (returned 207 coin (some candidate) actual), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (comparisonResult coin candidate actual).1, trace⟩ :=
  NativeDeterministic.finish_timed code oracle state trace 35 _ _ _
    (comparison_full_checked coin candidate actual) 35 (comparison_halts coin candidate actual).2

noncomputable def executionLaw {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) : PMF (Configuration State) :=
  (world state (firstMessage coin)).bind fun first =>
    (world first.1 (secondMessage first.2)).bind fun second =>
      (world second.1 (firstMessage coin)).bind fun repeated =>
        (world repeated.1 7).map fun actual =>
          ⟨actual.1, .running (comparisonResult coin (if coin then repeated.2 else second.2) actual.2).1,
            extendTrace 7 actual.2 (extendTrace (firstMessage coin) repeated.2
              (extendTrace (secondMessage first.2) second.2 (extendTrace (firstMessage coin) first.2 trace)))⟩

theorem after_coin_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 285
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) = executionLaw world state trace coin := by
  have duration : 285 = 48 + (48 + ((if coin then 1 else 59) + (48 + ((if coin then 59 else 1) + (46 + 35))))) := by
    cases coin <;> decide
  unfold executionLaw
  rw [duration, TimedExecution.eval_add, first_given_coin_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext first
  rw [TimedExecution.eval_add, second_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext second
  rw [TimedExecution.eval_add, select_second_run, PMF.pure_bind,
    TimedExecution.eval_add, third_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext repeated
  rw [TimedExecution.eval_add, select_candidate_run, PMF.pure_bind,
    TimedExecution.eval_add, last_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  change ((world repeated.1 7).bind fun actual =>
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 35
      ⟨actual.1, .running (returned 207 coin (some (if coin then repeated.2 else second.2)) actual.2),
        extendTrace 7 actual.2 (extendTrace (firstMessage coin) repeated.2
          (extendTrace (secondMessage first.2) second.2 (extendTrace (firstMessage coin) first.2 trace)))⟩) = _
  rw [PMF.map]
  congr 1
  funext actual
  exact comparison_run (packetOracle world) actual.1 _ coin _ actual.2

theorem whole_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 286
      (⟨state, .running {}, trace⟩ : Configuration State) = sampleBit.bind (executionLaw world state trace) := by
  rw [TimedExecution.eval, initial_step, PMF.bind_map]
  change (sampleBit.bind (fun coin => TimedExecution.eval (Reification.timedStep code (packetOracle world))
    285 (⟨state, .running (afterCoin coin), trace⟩ : Configuration State))) = _
  simp only [after_coin_run]

theorem execution_properties {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (final : Configuration State)
    (supported : final ∈ (executionLaw world state trace coin).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [executionLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨first, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨second, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨repeated, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  exact ⟨(comparison_halts coin _ actual.2).1, by simp [extendTrace]⟩

theorem whole_halts_queries {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (final : Configuration State)
    (supported : final ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) 286
      (⟨state, .running {}, trace⟩ : Configuration State)).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [whole_run, PMF.mem_support_bind_iff] at supported
  obtain ⟨coin, _, supported⟩ := supported
  exact execution_properties world state trace coin final supported

theorem haltsWithin {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    Reification.HaltsWithin code (packetOracle world) ⟨state, .running {}, trace⟩ 286 := by
  intro final supported
  rw [← Reification.timed_eval_eq] at supported
  exact (whole_halts_queries world state trace final supported).1

theorem observation_law {State : Type} (world : Oracle Message Tag State) (state : State) :
    (TimedExecution.eval (Reification.timedStep code (packetOracle world)) 286
      (⟨state, .running {}, []⟩ : Configuration State)).map RandomFunctionMACNativeCaller.Native.observe =
      target.run world state := by
  rw [whole_run]
  simp [executionLaw, RandomFunctionMACNativeCaller.Native.observe, RandomFunctionMACNativeCaller.Native.verdict,
    target, CryptoOracle.Program.run, PMF.bind_bind, PMF.map, Function.comp_def, comparison_decision, extendTrace]

end Foundation.Symmetric.RandomFunctionMACNativeOptimized
