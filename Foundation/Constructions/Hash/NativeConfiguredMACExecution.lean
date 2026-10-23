import Foundation.Constructions.Hash.NativeConfiguredMACRound
import Foundation.Constructions.Hash.NativeConfiguredMACChecked

/-! The actual optimized/analysis-linked caller and physical compact cache
execute in one outer runtime. Query caps compose with real retained frames;
setup and final analysis use accepted native traces without handoff resets. -/
namespace Foundation.Hash.Native.ConfiguredMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
open CompactMACRound (Retained Control)
open ConfiguredMACRound
open ConfiguredMACChecked (callerCode finishMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

abbrev Output (State Source : Type) := Retained State × Configuration Source

def embed {State Source : Type} (output : Output State Source) : Control State Source :=
  .source output.1.saved output.2

variable (mask : List Bool) {State Source Middle : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)

noncomputable def follow (first : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit Middle)
    (next : Middle → Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source))
    (handoff : ∀ middle ∈ (first.semantics ()).support, (next middle).entry () = first.exit () middle)
    (cap : Nat) (bound : ∀ middle ∈ (first.semantics ()).support, (next middle).budget () ≤ cap)
    (exit : ∀ middle output, (next middle).exit () output = embed output) :
    Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  (first.seq (Procedure.dispatch next) (fun _ => handoff) (fun _ => cap) (fun _ => bound)).observe Prod.snd
    (fun _ output => embed output) (fun _ result _ => (exit result.1 result.2).symm)

theorem follow_semantics (first : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit Middle)
    (next : Middle → Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source))
    (handoff : ∀ middle ∈ (first.semantics ()).support, (next middle).entry () = first.exit () middle)
    (cap : Nat) (bound : ∀ middle ∈ (first.semantics ()).support, (next middle).budget () ≤ cap)
    (exit : ∀ middle output, (next middle).exit () output = embed output) :
    (follow mask oracle callerOracle first next handoff cap bound exit).semantics () =
      (first.semantics ()).bind (fun middle => (next middle).semantics ()) := by
  simp only [follow, Procedure.observe, Procedure.seq, Procedure.dispatch, PMF.map_bind,
    PMF.map_comp, Function.comp_def]
  simp only [show (fun x : Output State Source => x) = id by rfl, PMF.map_id]

variable (ret : Retained State) (callerState : Source) (trace : List (List Bool × List Bool))

noncomputable def finish (coin : Bool) (candidate actual : Tag) :
    Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  (nativeSegment (callerCode mask) oracle callerOracle ret callerState trace
    ((1 + (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).2) + (3 * mask.length + 4))
    (Native.returned 207 coin (some candidate) actual) (finishMachine mask coin candidate actual)
    (ConfiguredMACChecked.finish_checked mask coin candidate actual)).observe
      (fun _ => (ret, ⟨callerState, .running (finishMachine mask coin candidate actual), trace⟩))
      (fun _ output => embed output) (fun _ _ _ => rfl)

theorem finish_bound (coin : Bool) (candidate actual : Tag) :
    (finish mask oracle callerOracle ret callerState trace coin candidate actual).budget () ≤ 39 + 3 * mask.length := by
  have bound := (RandomFunctionMACNativeOptimized.comparison_halts coin candidate actual).2
  change (1 + (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).2) + (3 * mask.length + 4) ≤ _
  omega

noncomputable def firstQuery (coin : Bool) : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed (callerCode mask) oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (ConfiguredMACChecked.call_fetch mask 15 (by decide_cbv)) rfl 12 (Native.afterCoin coin) (ConfiguredMACChecked.first_checked mask coin)

theorem firstQuery_bound (coin : Bool) :
    (firstQuery mask oracle callerOracle ret callerState trace coin).budget () ≤ 146 * ret.table.length + 266 := by
  have bound := prefixed_bound (callerCode mask) oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (ConfiguredMACChecked.call_fetch mask 15 (by decide_cbv)) rfl 12 (Native.afterCoin coin) (ConfiguredMACChecked.first_checked mask coin)
  apply le_trans bound
  cases coin <;> simp only [Bool.false_eq_true, if_false, if_true] at bound ⊢ <;> omega

theorem firstQuery_growth (coin : Bool) (output : Retained State × Tag)
    (supported : output ∈ ((firstQuery mask oracle callerOracle ret callerState trace coin).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth (callerCode mask) oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (ConfiguredMACChecked.call_fetch mask 15 (by decide_cbv)) rfl 12 (Native.afterCoin coin) (ConfiguredMACChecked.first_checked mask coin) output supported

noncomputable def secondQuery (coin : Bool) (first : Tag) : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed (callerCode mask) oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (ConfiguredMACChecked.call_fetch mask 30 (by decide_cbv)) rfl 12 (Native.returned 16 coin none first) (ConfiguredMACChecked.second_checked mask coin first)

theorem secondQuery_bound (coin : Bool) (first : Tag) :
    (secondQuery mask oracle callerOracle ret callerState trace coin first).budget () ≤ 146 * ret.table.length + 266 := by
  have bound := prefixed_bound (callerCode mask) oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (ConfiguredMACChecked.call_fetch mask 30 (by decide_cbv)) rfl 12 (Native.returned 16 coin none first) (ConfiguredMACChecked.second_checked mask coin first)
  apply le_trans bound
  cases coin <;> simp only [Bool.false_eq_true, if_false, if_true] at bound ⊢ <;> omega

theorem secondQuery_growth (coin : Bool) (first : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((secondQuery mask oracle callerOracle ret callerState trace coin first).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth (callerCode mask) oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (ConfiguredMACChecked.call_fetch mask 30 (by decide_cbv)) rfl 12 (Native.returned 16 coin none first) (ConfiguredMACChecked.second_checked mask coin first) output supported

noncomputable def repeatedQuery (coin : Bool) (second : Tag) : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.thirdCall coin (RandomFunctionMACNativeOptimized.savedSecond coin second) second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (ConfiguredMACChecked.call_fetch mask 120 (by decide_cbv)) rfl ((if coin then 1 else 59) + 12) (Native.returned 31 coin none second) (ConfiguredMACChecked.repeated_checked mask coin second)

theorem repeatedQuery_bound (coin : Bool) (second : Tag) :
    (repeatedQuery mask oracle callerOracle ret callerState trace coin second).budget () ≤ 146 * ret.table.length + 325 := by
  have bound := prefixed_bound (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.thirdCall coin (RandomFunctionMACNativeOptimized.savedSecond coin second) second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (ConfiguredMACChecked.call_fetch mask 120 (by decide_cbv)) rfl ((if coin then 1 else 59) + 12) (Native.returned 31 coin none second) (ConfiguredMACChecked.repeated_checked mask coin second)
  apply le_trans bound
  cases coin <;> simp only [Bool.false_eq_true, if_false, if_true] at bound ⊢ <;> omega

theorem repeatedQuery_growth (coin : Bool) (second : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((repeatedQuery mask oracle callerOracle ret callerState trace coin second).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.thirdCall coin (RandomFunctionMACNativeOptimized.savedSecond coin second) second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (ConfiguredMACChecked.call_fetch mask 120 (by decide_cbv)) rfl ((if coin then 1 else 59) + 12) (Native.returned 31 coin none second) (ConfiguredMACChecked.repeated_checked mask coin second) output supported

noncomputable def verifyQuery (coin : Bool) (second repeated : Tag) : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (ConfiguredMACChecked.call_fetch mask 206 (by decide_cbv)) rfl ((if coin then 59 else 1) + 10) (Native.returned 121 coin (RandomFunctionMACNativeOptimized.savedSecond coin second) repeated) (ConfiguredMACChecked.verify_checked mask coin second repeated)

theorem verifyQuery_bound (coin : Bool) (second repeated : Tag) :
    (verifyQuery mask oracle callerOracle ret callerState trace coin second repeated).budget () ≤ 146 * ret.table.length + 323 := by
  have bound := prefixed_bound (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (ConfiguredMACChecked.call_fetch mask 206 (by decide_cbv)) rfl ((if coin then 59 else 1) + 10) (Native.returned 121 coin (RandomFunctionMACNativeOptimized.savedSecond coin second) repeated) (ConfiguredMACChecked.verify_checked mask coin second repeated)
  apply le_trans bound
  cases coin <;> simp only [Bool.false_eq_true, if_false, if_true] at bound ⊢ <;> omega

theorem verifyQuery_growth (coin : Bool) (second repeated : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((verifyQuery mask oracle callerOracle ret callerState trace coin second repeated).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth (callerCode mask) oracle callerOracle ret (RandomFunctionMACNativeOptimized.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (ConfiguredMACChecked.call_fetch mask 206 (by decide_cbv)) rfl ((if coin then 59 else 1) + 10) (Native.returned 121 coin (RandomFunctionMACNativeOptimized.savedSecond coin second) repeated) (ConfiguredMACChecked.verify_checked mask coin second repeated) output supported

noncomputable def last (coin : Bool) (second repeated : Tag) :
    Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  follow mask oracle callerOracle (verifyQuery mask oracle callerOracle ret callerState trace coin second repeated)
    (fun answer => finish mask oracle callerOracle answer.1 callerState (Native.extendTrace 7 answer.2 trace)
      coin (if coin then repeated else second) answer.2)
    (fun _ _ => rfl) (39 + 3 * mask.length) (fun _ _ => finish_bound ..) (fun _ _ => rfl)

theorem last_bound (coin : Bool) (second repeated : Tag) :
    (last mask oracle callerOracle ret callerState trace coin second repeated).budget () ≤ 146 * ret.table.length + 362 + 3 * mask.length := by
  change (verifyQuery mask oracle callerOracle ret callerState trace coin second repeated).budget () + (39 + 3 * mask.length) ≤ _
  have bound := verifyQuery_bound mask oracle callerOracle ret callerState trace coin second repeated
  omega

noncomputable def repeatedStage (coin : Bool) (second : Tag) :
    Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  follow mask oracle callerOracle (repeatedQuery mask oracle callerOracle ret callerState trace coin second)
    (fun answer => last mask oracle callerOracle answer.1 callerState
      (Native.extendTrace (firstMessage coin) answer.2 trace) coin second answer.2)
    (fun _ _ => rfl) (146 * (ret.table.length + 1) + 362 + 3 * mask.length) (by
      intro answer supported
      have bound := last_bound mask oracle callerOracle answer.1 callerState
        (Native.extendTrace (firstMessage coin) answer.2 trace) coin second answer.2
      have growth := repeatedQuery_growth mask oracle callerOracle ret callerState trace coin second answer supported
      omega) (fun _ _ => rfl)

theorem repeat_bound (coin : Bool) (second : Tag) :
    (repeatedStage mask oracle callerOracle ret callerState trace coin second).budget () ≤ 292 * ret.table.length + 833 + 3 * mask.length := by
  change (repeatedQuery mask oracle callerOracle ret callerState trace coin second).budget () +
    (146 * (ret.table.length + 1) + 362 + 3 * mask.length) ≤ _
  have bound := repeatedQuery_bound mask oracle callerOracle ret callerState trace coin second
  omega

noncomputable def second (coin : Bool) (first : Tag) :
    Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  follow mask oracle callerOracle (secondQuery mask oracle callerOracle ret callerState trace coin first)
    (fun answer => repeatedStage mask oracle callerOracle answer.1 callerState
      (Native.extendTrace (secondMessage first) answer.2 trace) coin answer.2)
    (fun _ _ => rfl) (292 * (ret.table.length + 1) + 833 + 3 * mask.length) (by
      intro answer supported
      have bound := repeat_bound mask oracle callerOracle answer.1 callerState
        (Native.extendTrace (secondMessage first) answer.2 trace) coin answer.2
      have growth := secondQuery_growth mask oracle callerOracle ret callerState trace coin first answer supported
      omega) (fun _ _ => rfl)

theorem second_bound (coin : Bool) (first : Tag) :
    (second mask oracle callerOracle ret callerState trace coin first).budget () ≤ 438 * ret.table.length + 1391 + 3 * mask.length := by
  change (secondQuery mask oracle callerOracle ret callerState trace coin first).budget () +
    (292 * (ret.table.length + 1) + 833 + 3 * mask.length) ≤ _
  have bound := secondQuery_bound mask oracle callerOracle ret callerState trace coin first
  omega

noncomputable def first (coin : Bool) : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  follow mask oracle callerOracle (firstQuery mask oracle callerOracle ret callerState trace coin)
    (fun answer => second mask oracle callerOracle answer.1 callerState
      (Native.extendTrace (firstMessage coin) answer.2 trace) coin answer.2)
    (fun _ _ => rfl) (438 * (ret.table.length + 1) + 1391 + 3 * mask.length) (by
      intro answer supported
      have bound := second_bound mask oracle callerOracle answer.1 callerState
        (Native.extendTrace (firstMessage coin) answer.2 trace) coin answer.2
      have growth := firstQuery_growth mask oracle callerOracle ret callerState trace coin answer supported
      omega) (fun _ _ => rfl)

theorem first_bound (coin : Bool) :
    (first mask oracle callerOracle ret callerState trace coin).budget () ≤ 584 * ret.table.length + 2095 + 3 * mask.length := by
  change (firstQuery mask oracle callerOracle ret callerState trace coin).budget () +
    (438 * (ret.table.length + 1) + 1391 + 3 * mask.length) ≤ _
  have bound := firstQuery_bound mask oracle callerOracle ret callerState trace coin
  omega

noncomputable def coin : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit Bool :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .running {}, trace⟩)
    (fun _ coin => .source ret.saved ⟨callerState, .running (Native.afterCoin coin), trace⟩)
    (fun _ => sampleBit) (fun _ => 1) (by
      intro _
      simp only [TimedExecution.eval, PMF.bind_pure]
      change (Reification.timedStep (callerCode mask) callerOracle ⟨callerState, .running {}, trace⟩).map
        (PacketResponseSource.Control.source ret.saved) = _
      rw [ConfiguredMACChecked.initial_step, PMF.map_comp]
      rfl)

noncomputable def whole : Procedure (ConfiguredMACRound.step (callerCode mask) oracle callerOracle) Unit (Output State Source) :=
  follow mask oracle callerOracle (coin mask oracle callerOracle ret callerState trace)
    (first mask oracle callerOracle ret callerState trace) (fun _ _ => rfl)
    (584 * ret.table.length + 2095 + 3 * mask.length) (fun _ _ => first_bound ..) (fun _ _ => rfl)

theorem whole_budget : (whole mask oracle callerOracle ret callerState trace).budget () = 584 * ret.table.length + 2096 + 3 * mask.length := by
  change 1 + (584 * ret.table.length + 2095 + 3 * mask.length) = _
  omega

end Foundation.Hash.Native.ConfiguredMACExecution
