import Foundation.Examples.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrival

/-! A variable-time native link with deliberately loose bounds. The source
halts after 3 or 4 steps, its source certificate allows 9, and the one-step
second component is allotted 7. The linked budget is 17 but actual first
halts take 5 or 6, including the second call and final caller halt. -/
namespace Foundation.Examples.NativeVariableTimeLink
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable def loose : NativeComponent Tape Configuration :=
  NativeComponent.ofFixed NativeFirstArrival.padded.procedure.code
    NativeFirstArrival.padded.procedure.execution.entry (fun _ state => state)
    NativeFirstArrival.padded.procedure.execution.semantics (fun _ => 9)
    (fun input => NativeFirstArrival.padded.procedure.final_run input
      (NativeFirstArrival.padded.halted input) 9 (by change 4 ≤ 9; decide))
    (by decide) NativeFirstArrival.padded.entry NativeFirstArrival.padded.active NativeFirstArrival.padded.halted

theorem loose_joint (input : Tape) :
    loose.firstArrival.procedure.execution.costed input =
      sampleBit.map (fun bit => (RankedVariableTime.finish input bit, if bit then 4 else 3)) := by
  rw [loose.firstArrival_costed_eq_of_code_entry NativeFirstArrival.padded input rfl rfl,
    NativeFirstArrival.actual_joint]

theorem loose_semantics (input : Tape) :
    loose.procedure.execution.semantics input = sampleBit.map (RankedVariableTime.finish input) := by
  have h := congrArg (fun distribution => distribution.map Prod.fst) (loose_joint input)
  rw [loose.firstArrival.procedure.execution.correct, loose.firstArrival_semantics, PMF.map_comp] at h
  change (loose.procedure.execution.semantics input).map id =
    sampleBit.map (RankedVariableTime.finish input) at h
  simpa only [PMF.map_id] using h

noncomputable def stop : NativeComponent Configuration Configuration :=
  NativeComponent.ofFixed [.halt] (fun state => state.resumeAt 0) (fun _ state => state)
    (fun state => PMF.pure {state.resumeAt 0 with halted := true}) (fun _ => 1)
    (fun state => by simp [evalConfigWithin, stepPMF, next, Configuration.resumeAt, Instruction.next,
      PMF.pure_bind, PMF.pure_map])
    (by decide) (fun _ => by change 0 < 1; decide) (fun _ => rfl)
    (by intro _ result h; rw [PMF.mem_support_pure_iff] at h; subst result; rfl)

noncomputable def linked : TypedNativeComposition.Link loose.procedure stop.procedure :=
  loose.link stop (fun _ state => {state.resumeAt 2 with halted := true})
    (by
      intro input output hOutput
      rw [loose_semantics, PMF.mem_support_map_iff] at hOutput
      obtain ⟨bit, _, rfl⟩ := hOutput
      rfl)
    (fun _ output => output)
    (by
      intro _ output _
      change (output.resumeAt 0).rebasePc 5 = output.resumeAt 5
      simp [Configuration.resumeAt, Configuration.rebasePc])
    (fun _ => 7) (fun _ _ _ => by change 1 ≤ 7; decide)

theorem budget (input : Tape) : linked.native.execution.budget input = 17 := rfl

theorem stop_joint (input : Configuration) :
    stop.firstArrival.procedure.execution.costed input =
      PMF.pure ({input.resumeAt 0 with halted := true}, 1) := by
  rw [stop.firstArrival_costed]
  change runToBoundary (stepPMF [.halt]) Configuration.halted 1 (input.resumeAt 0) = _
  simp [runToBoundary, stepPMF, next, Configuration.resumeAt, Instruction.next, PMF.pure_bind, PMF.pure_map]

theorem actual_joint (input : Tape) :
    linked.component.firstArrival.procedure.execution.costed input =
      sampleBit.map (fun bit =>
        ({(RankedVariableTime.finish input bit).resumeAt 7 with halted := true}, if bit then 6 else 5)) := by
  rw [linked.firstArrival_costed, linked.first_costed_of_arrival]
  change ((loose.firstArrival.procedure.execution.costed input).map
    (fun result => ((input, {(result.1.resumeAt linked.entryPc).resumeAt 2 with halted := true}), result.2))).bind _ = _
  rw [loose_joint, PMF.map_comp, PMF.bind_map]
  change sampleBit.bind _ = sampleBit.bind _
  congr 1
  funext bit
  dsimp only [Function.comp_def]
  rw [linked.second_costed_of_arrival]
  change ((stop.firstArrival.procedure.execution.costed (RankedVariableTime.finish input bit)).map
    (fun result => (result.1.resumeAt linked.finalPc, result.2))).map _ = _
  rw [stop_joint, PMF.pure_map, PMF.pure_map]
  cases bit <;> rfl

theorem time_distribution (input : Tape) :
    (linked.component.firstArrival.procedure.execution.costed input).map Prod.snd =
      sampleBit.map (fun bit => if bit then 6 else 5) := by
  rw [actual_joint, PMF.map_comp]
  rfl

end Foundation.Examples.NativeVariableTimeLink
