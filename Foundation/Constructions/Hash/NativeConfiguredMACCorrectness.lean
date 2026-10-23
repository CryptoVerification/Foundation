import Foundation.Constructions.Hash.NativeConfiguredMACExecution

/-! Stopping, exact transcript length and actual-time reachability of the
complete four-call execution. All bounds apply to the continuing physical
runtime, including the server internals and native caller instructions. -/
namespace Foundation.Hash.Native.ConfiguredMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
open CompactMACRound (Retained Control)
open ConfiguredMACRound
open ConfiguredMACChecked (callerCode finishMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

variable (mask : List Bool) {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (callerState : Source) (trace : List (List Bool × List Bool))

def Post (calls : Nat) (output : Output State Source) : Prop :=
  (∃ machine : Machine.Configuration, output.2.control = .running machine ∧ machine.halted = true) ∧
  output.2.state = callerState ∧ output.2.reverseTrace.length = trace.length + calls ∧
  output.1.table.length ≤ ret.table.length + calls

theorem post_prepend (next : Retained State) (message : Message) (tag : Tag) (calls : Nat)
    (output : Output State Source)
    (post : Post next callerState (Native.extendTrace message tag trace) calls output)
    (growth : next.table.length ≤ ret.table.length + 1) : Post ret callerState trace (calls + 1) output := by
  obtain ⟨halted, state, length, size⟩ := post
  refine ⟨halted, state, ?_, ?_⟩
  · simpa only [Native.extendTrace, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using length
  · omega

theorem finish_post (coin : Bool) (candidate actual : Tag) (output : Output State Source)
    (supported : output ∈ ((finish mask oracle callerOracle ret callerState trace coin candidate actual).semantics ()).support) :
    Post ret callerState trace 0 output := by
  simp only [finish, Procedure.observe, nativeSegment, TimedExecution.Procedure.ofFixed,
    PMF.pure_map, PMF.mem_support_pure_iff] at supported
  subst output
  exact ⟨⟨_, rfl, rfl⟩, rfl, by simp, by simp⟩

theorem last_post (coin : Bool) (second repeated : Tag) (output : Output State Source)
    (supported : output ∈ ((last mask oracle callerOracle ret callerState trace coin second repeated).semantics ()).support) :
    Post ret callerState trace 1 output := by
  unfold last at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, ha, ho⟩ := supported
  exact post_prepend ret callerState trace answer.1 7 answer.2 0 output
    (finish_post mask oracle callerOracle answer.1 callerState (Native.extendTrace 7 answer.2 trace)
      coin (if coin then repeated else second) answer.2 output ho)
    (verifyQuery_growth mask oracle callerOracle ret callerState trace coin second repeated answer ha)

theorem repeat_post (coin : Bool) (second : Tag) (output : Output State Source)
    (supported : output ∈ ((repeatedStage mask oracle callerOracle ret callerState trace coin second).semantics ()).support) :
    Post ret callerState trace 2 output := by
  unfold repeatedStage at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, ha, ho⟩ := supported
  exact post_prepend ret callerState trace answer.1 (firstMessage coin) answer.2 1 output
    (last_post mask oracle callerOracle answer.1 callerState (Native.extendTrace (firstMessage coin) answer.2 trace)
      coin second answer.2 output ho)
    (repeatedQuery_growth mask oracle callerOracle ret callerState trace coin second answer ha)

theorem second_post (coin : Bool) (first : Tag) (output : Output State Source)
    (supported : output ∈ ((second mask oracle callerOracle ret callerState trace coin first).semantics ()).support) :
    Post ret callerState trace 3 output := by
  unfold second at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, ha, ho⟩ := supported
  exact post_prepend ret callerState trace answer.1 (secondMessage first) answer.2 2 output
    (repeat_post mask oracle callerOracle answer.1 callerState (Native.extendTrace (secondMessage first) answer.2 trace)
      coin answer.2 output ho)
    (secondQuery_growth mask oracle callerOracle ret callerState trace coin first answer ha)

theorem first_post (coin : Bool) (output : Output State Source)
    (supported : output ∈ ((first mask oracle callerOracle ret callerState trace coin).semantics ()).support) :
    Post ret callerState trace 4 output := by
  unfold first at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, ha, ho⟩ := supported
  exact post_prepend ret callerState trace answer.1 (firstMessage coin) answer.2 3 output
    (second_post mask oracle callerOracle answer.1 callerState (Native.extendTrace (firstMessage coin) answer.2 trace)
      coin answer.2 output ho)
    (firstQuery_growth mask oracle callerOracle ret callerState trace coin answer ha)

theorem whole_post (output : Output State Source)
    (supported : output ∈ ((whole mask oracle callerOracle ret callerState trace).semantics ()).support) :
    Post ret callerState trace 4 output := by
  unfold whole at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨coin, _, ho⟩ := supported
  exact first_post mask oracle callerOracle ret callerState trace coin output ho

/-- Every full physical caller endpoint has the same adaptive requests,
response reuse, candidate selection and final comparison as the original
MAC example. This support statement does not assert response probabilities. -/
theorem whole_shape (output : Output State Source)
    (supported : output ∈ ((whole mask oracle callerOracle ret callerState trace).semantics ()).support) :
    ∃ (coin : Bool) (first second repeated actual : Tag),
      output.2 = ⟨callerState,
        .running (finishMachine mask coin (if coin then repeated else second) actual),
        Native.extendTrace 7 actual (Native.extendTrace (firstMessage coin) repeated
          (Native.extendTrace (secondMessage first) second (Native.extendTrace (firstMessage coin) first trace)))⟩ := by
  unfold whole at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨coin, _, supported⟩ := supported
  unfold first at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨firstAnswer, _, supported⟩ := supported
  unfold second at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨secondAnswer, _, supported⟩ := supported
  unfold repeatedStage at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨repeatAnswer, _, supported⟩ := supported
  unfold last at supported
  rw [follow_semantics, PMF.mem_support_bind_iff] at supported
  obtain ⟨actualAnswer, _, supported⟩ := supported
  simp only [finish, Procedure.observe, nativeSegment, TimedExecution.Procedure.ofFixed,
    PMF.pure_map, PMF.mem_support_pure_iff] at supported
  subst output
  exact ⟨coin, firstAnswer.2, secondAnswer.2, repeatAnswer.2, actualAnswer.2, rfl⟩

theorem last_operational (coin : Bool) (second repeated : Tag) :
    Procedure.Operational (last mask oracle callerOracle ret callerState trace coin second repeated) := by
  unfold last follow
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold verifyQuery
    apply prefixed_operational
  · apply Procedure.operational_dispatch
    intro answer
    unfold finish
    apply Procedure.operational_observe
    apply Procedure.operational_ofFixed

theorem repeat_operational (coin : Bool) (second : Tag) :
    Procedure.Operational (repeatedStage mask oracle callerOracle ret callerState trace coin second) := by
  unfold repeatedStage follow
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold repeatedQuery
    apply prefixed_operational
  · apply Procedure.operational_dispatch
    intro answer
    apply last_operational

theorem second_operational (coin : Bool) (first : Tag) :
    Procedure.Operational (second mask oracle callerOracle ret callerState trace coin first) := by
  unfold second follow
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold secondQuery
    apply prefixed_operational
  · apply Procedure.operational_dispatch
    intro answer
    apply repeat_operational

theorem first_operational (coin : Bool) :
    Procedure.Operational (first mask oracle callerOracle ret callerState trace coin) := by
  unfold first follow
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold firstQuery
    apply prefixed_operational
  · apply Procedure.operational_dispatch
    intro answer
    apply second_operational

theorem whole_operational : Procedure.Operational (whole mask oracle callerOracle ret callerState trace) := by
  unfold whole follow
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold coin
    apply Procedure.operational_ofFixed
  · apply Procedure.operational_dispatch
    intro coin
    apply first_operational

theorem stopped_absorbing (output : Output State Source) (post : Post ret callerState trace 4 output) :
    ConfiguredMACRound.step (callerCode mask) oracle callerOracle (embed output) = PMF.pure (embed output) := by
  obtain ⟨machine, control, halted⟩ := post.1
  rcases output with ⟨saved, state, current, history⟩
  dsimp only at control
  subst current
  simp [ConfiguredMACRound.step, embed, PacketResponseSource.step, Reification.timedStep, Reification.terminal, halted, PMF.pure_map]

/-- Full continuing execution from the original caller entry. The bound
includes four cache services, request/response transfer, native adaptive
selection, candidate copies and the final comparison/real halt. -/
theorem whole_run (horizon : Nat) (enough : 584 * ret.table.length + 2096 + 3 * mask.length ≤ horizon) :
    TimedExecution.eval (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) horizon
      (.source ret.saved ⟨callerState, .running {}, trace⟩) =
      ((whole mask oracle callerOracle ret callerState trace).semantics ()).map embed := by
  apply (whole mask oracle callerOracle ret callerState trace).final_run ()
  · intro output supported
    exact stopped_absorbing mask oracle callerOracle ret callerState trace output
      (whole_post mask oracle callerOracle ret callerState trace output supported)
  · rw [whole_budget]
    exact enough

/-- Every actual reported return is reached at that time, with all four
calls recorded and a retained reusable private cache. -/
theorem whole_costed (result : Output State Source × Nat)
    (supported : result ∈ ((whole mask oracle callerOracle ret callerState trace).costed ()).support) :
    embed result.1 ∈ (TimedExecution.eval (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) result.2
      (.source ret.saved ⟨callerState, .running {}, trace⟩)).support ∧
    result.2 ≤ 584 * ret.table.length + 2096 + 3 * mask.length ∧ Post ret callerState trace 4 result.1 := by
  refine ⟨whole_operational mask oracle callerOracle ret callerState trace () result supported, ?_, ?_⟩
  · have bounded := (whole mask oracle callerOracle ret callerState trace).bounded () result supported
    rwa [whole_budget] at bounded
  · exact whole_post mask oracle callerOracle ret callerState trace result.1
      ((whole mask oracle callerOracle ret callerState trace).result_support () result supported)

end Foundation.Hash.Native.ConfiguredMACExecution
