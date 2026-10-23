import Foundation.Constructions.Symmetric.RandomFunctionMACNativeComparison

/-! Whole continuing caller execution for the adaptive MAC. Every response
and both local-coin choices are covered. The 343-transition bound counts all
native work and packet transfer; each oracle-internal evaluation remains one
external capability invocation, rather than an unproved server-time bound.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem first_given_coin_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 16 coin none answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, first_setup_native, PMF.pure_bind, first_transfer]
  simp only [packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, firstCall, returned, machineAt, memory, extendTrace]

theorem save_second_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 58
      (⟨state, .running (returned 31 coin none second), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (returned 105 coin (some second) second), trace⟩ := by
  simpa only [saveAddress, savedAddress, Bool.false_eq_true, if_false] using
    save_tag_run oracle state trace false coin none second

/-- The reference joint law retains the actual final native configuration,
oracle state and all four request/response pairs, including repeats. -/
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
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 342
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) = executionLaw world state trace coin := by
  have duration : 342 = 48 + (48 + (58 + (48 + ((if coin then 59 else 1) +
      (46 + (if coin then 35 else 93)))))) := by cases coin <;> decide
  unfold executionLaw
  rw [duration, TimedExecution.eval_add, first_given_coin_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext first
  rw [TimedExecution.eval_add, second_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext second
  rw [TimedExecution.eval_add, save_second_run, PMF.pure_bind,
    TimedExecution.eval_add, third_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext repeated
  rw [TimedExecution.eval_add, select_candidate_run, PMF.pure_bind,
    TimedExecution.eval_add, last_query_run, PMF.bind_map]
  simp only [Function.comp_def]
  change ((world repeated.1 7).bind fun actual =>
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) (if coin then 35 else 93)
      ⟨actual.1, .running (returned 206 coin (some (if coin then repeated.2 else second.2)) actual.2),
        extendTrace 7 actual.2 (extendTrace (firstMessage coin) repeated.2
          (extendTrace (secondMessage first.2) second.2 (extendTrace (firstMessage coin) first.2 trace)))⟩) = _
  rw [PMF.map]
  congr 1
  funext actual
  exact comparison_run (packetOracle world) actual.1 _ coin _ actual.2 (if coin then 35 else 93)
    (by cases coin <;> decide)

/-- Universal full-frame execution law, starting the machine only once.
The surplus in a short branch pads only after its actual native halt. -/
theorem whole_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 343
      (⟨state, .running {}, trace⟩ : Configuration State) =
      sampleBit.bind (executionLaw world state trace) := by
  rw [TimedExecution.eval, initial_step, PMF.bind_map]
  change (sampleBit.bind (fun coin => TimedExecution.eval (Reification.timedStep code (packetOracle world))
    342 (⟨state, .running (afterCoin coin), trace⟩ : Configuration State))) = _
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
    (supported : final ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) 343
      (⟨state, .running {}, trace⟩ : Configuration State)).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [whole_run, PMF.mem_support_bind_iff] at supported
  obtain ⟨coin, _, supported⟩ := supported
  exact execution_properties world state trace coin final supported

theorem haltsWithin {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    Reification.HaltsWithin code (packetOracle world) ⟨state, .running {}, trace⟩ 343 := by
  intro final supported
  rw [← Reification.timed_eval_eq] at supported
  exact (whole_halts_queries world state trace final supported).1

def verdict : Control → Bool
  | .running machine => machine.outputTape.current.getD false
  | _ => false

def observe {State : Type} (final : Configuration State) : Outcome Message Tag Bool State :=
  ⟨verdict final.control, final.state,
    final.reverseTrace.reverse.map (fun entry => (decodeMessage entry.1, decodeTag entry.2))⟩

/-- Complete refinement of the caller to the SAME adaptive four-query game,
not merely an endpoint success-probability comparison. -/
theorem observation_law {State : Type} (world : Oracle Message Tag State) (state : State) :
    (TimedExecution.eval (Reification.timedStep code (packetOracle world)) 343
      (⟨state, .running {}, []⟩ : Configuration State)).map observe = target.run world state := by
  rw [whole_run]
  simp [executionLaw, observe, verdict, target, CryptoOracle.Program.run,
    PMF.bind_bind, PMF.map, Function.comp_def, comparison_decision, extendTrace]

theorem verdict_law {State : Type} (world : Oracle Message Tag State) (state : State) :
    (TimedExecution.eval (Reification.timedStep code (packetOracle world)) 343
      (⟨state, .running {}, []⟩ : Configuration State)).map (fun final => verdict final.control) =
      (target.run world state).map Outcome.result := by
  have projected := congrArg (PMF.map Outcome.result) (observation_law world state)
  simpa only [PMF.map_comp, observe, Function.comp_def] using projected

/-- This is the actual native caller, including its local computation and
packet transfer. The keyed oracle's internal evaluation is external. -/
noncomputable def familyGame {Key : Type} (keys : PMF Key) (evaluate : Key → Message → Tag) : PMF Bool :=
  keys.bind fun key =>
    (TimedExecution.eval (Reification.timedStep code (packetOracle (RandomOracle.eager (evaluate key)))) 343
      (⟨[], .running {}, []⟩ : Configuration (RandomOracle.Table Message Tag))).map
        (fun final => verdict final.control)

theorem family_game_eq {Key : Type} (keys : PMF Key) (evaluate : Key → Message → Tag) :
    familyGame keys evaluate = RandomFunctionMACSchedules.keyedGame keys evaluate
      RandomFunctionMACSchedules.Examples.attack := by
  simp only [familyGame, verdict_law, target_eq_checked, RandomFunctionMACSchedules.keyedGame,
    RandomFunctionMACSchedules.familyExperiment]

theorem ideal_security :
    eventProb (familyGame (uniform (Message → Tag)) id) (· = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [family_game_eq]
  have bound := RandomFunctionMACProofEdits.ideal_bound RandomFunctionMACSchedules.Examples.attack
  simpa only [RandomFunctionMACSchedules.idealExperiment, RandomFunctionMACSchedules.keyedGame,
    RandomFunctionMACSchedules.familyExperiment, RandomFunctionMACProofEdits.distinguisher_eq,
    Fintype.card_fin, Nat.cast_ofNat, id_eq] using bound

/-- Apply the assumption to the explicit distinguisher extracted from the
cache-dependent proof route. Its game agrees with this concrete native run. -/
theorem keyed_security {Key : Type} (keys : PMF Key) (evaluate : Key → Message → Tag) (epsilon : ℝ≥0∞)
    (prf : eventProb (RandomFunctionMACSchedules.familyExperiment keys evaluate
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack)) (· = true) ≤
      eventProb (RandomFunctionMACSchedules.idealExperiment
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack))
        (· = true) + epsilon) :
    eventProb (familyGame keys evaluate) (· = true) ≤ epsilon + (256 : ℝ≥0∞)⁻¹ := by
  rw [family_game_eq]
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using RandomFunctionMACProofEdits.cached_keyed_bound
    keys evaluate RandomFunctionMACSchedules.Examples.attack epsilon prf

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
