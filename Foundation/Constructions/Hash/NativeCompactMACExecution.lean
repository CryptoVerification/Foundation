import Foundation.Constructions.Hash.NativeCompactMACRound

/-! Four calls of the unchanged adaptive MAC caller in one continuing
physical runtime. Every handoff retains the actual server and caller frames.
Resource caps compose; actual durations are never replaced by padding at a
nonterminal caller boundary. -/
namespace Foundation.Hash.Native.CompactMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
open CompactMACRound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

abbrev Output (State Source : Type) := Retained State × Configuration Source

def embed {State Source : Type} (output : Output State Source) : Control State Source :=
  .source output.1.saved output.2

variable {State Source Middle : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)

noncomputable def follow (first : Procedure (step oracle callerOracle) Unit Middle)
    (next : Middle → Procedure (step oracle callerOracle) Unit (Output State Source))
    (handoff : ∀ middle ∈ (first.semantics ()).support, (next middle).entry () = first.exit () middle)
    (cap : Nat) (bound : ∀ middle ∈ (first.semantics ()).support, (next middle).budget () ≤ cap)
    (exit : ∀ middle output, (next middle).exit () output = embed output) :
    Procedure (step oracle callerOracle) Unit (Output State Source) :=
  (first.seq (Procedure.dispatch next) (fun _ => handoff) (fun _ => cap) (fun _ => bound)).observe Prod.snd
    (fun _ output => embed output) (fun _ result _ => (exit result.1 result.2).symm)

theorem follow_semantics (first : Procedure (step oracle callerOracle) Unit Middle)
    (next : Middle → Procedure (step oracle callerOracle) Unit (Output State Source))
    (handoff : ∀ middle ∈ (first.semantics ()).support, (next middle).entry () = first.exit () middle)
    (cap : Nat) (bound : ∀ middle ∈ (first.semantics ()).support, (next middle).budget () ≤ cap)
    (exit : ∀ middle output, (next middle).exit () output = embed output) :
    (follow oracle callerOracle first next handoff cap bound exit).semantics () =
      (first.semantics ()).bind (fun middle => (next middle).semantics ()) := by
  simp only [follow, Procedure.observe, Procedure.seq, Procedure.dispatch, PMF.map_bind,
    PMF.map_comp, Function.comp_def]
  simp only [show (fun x : Output State Source => x) = id by rfl, PMF.map_id]

variable (ret : Retained State) (callerState : Source) (trace : List (List Bool × List Bool))

noncomputable def finish (coin : Bool) (candidate actual : Tag) :
    Procedure (step oracle callerOracle) Unit (Output State Source) :=
  (nativeSegment oracle callerOracle ret callerState trace (1 + (Native.comparisonResult coin candidate actual).2)
    (Native.returned 206 coin (some candidate) actual) (Native.comparisonResult coin candidate actual).1
    (NativeDeterministic.finish_spec Native.code 35 _ _ _ (Native.comparison_full_checked coin candidate actual)).2.2).observe
      (fun _ => (ret, ⟨callerState, .running (Native.comparisonResult coin candidate actual).1, trace⟩))
      (fun _ output => embed output) (fun _ _ _ => rfl)

theorem finish_bound (coin : Bool) (candidate actual : Tag) :
    (finish oracle callerOracle ret callerState trace coin candidate actual).budget () ≤ 35 :=
  (Native.comparison_halts coin candidate actual).2

/-- Saving the second response and generating the repeatedStage request are
native instructions in the unchanged caller. -/
theorem repeated_checked (coin : Bool) (second : Tag) :
    NativeDeterministic.run Native.code 70 (Native.returned 31 coin none second) = some (Native.thirdCall coin second) := by
  rw [show 70 = 58 + 12 by decide, NativeDeterministic.run_add]
  have saved := Native.save_tag_checked false coin none second
  simp only [Native.saveAddress, Native.savedAddress, Bool.false_eq_true, if_false] at saved
  rw [saved, Option.bind_some, Native.third_setup_checked]

theorem verify_checked (coin : Bool) (second repeated : Tag) :
    NativeDeterministic.run Native.code ((if coin then 59 else 1) + 10)
      (Native.returned 120 coin (some second) repeated) =
      some (Native.lastCall coin (if coin then repeated else second) repeated) := by
  rw [NativeDeterministic.run_add, Native.select_candidate_checked, Option.bind_some, Native.last_setup_checked]

noncomputable def firstQuery (coin : Bool) : Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (Native.first_call_position coin) rfl 12 (Native.afterCoin coin) (Native.first_setup_checked coin)

theorem firstQuery_bound (coin : Bool) :
    (firstQuery oracle callerOracle ret callerState trace coin).budget () ≤ 146 * ret.table.length + 266 := by
  have bound := prefixed_bound oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (Native.first_call_position coin) rfl 12 (Native.afterCoin coin) (Native.first_setup_checked coin)
  apply le_trans bound
  omega

theorem firstQuery_growth (coin : Bool) (output : Retained State × Tag)
    (supported : output ∈ ((firstQuery oracle callerOracle ret callerState trace coin).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth oracle callerOracle ret (Native.firstCall coin) callerState trace (firstMessage coin) [] ([]) rfl (Native.first_call_position coin) rfl 12 (Native.afterCoin coin) (Native.first_setup_checked coin) output supported

noncomputable def secondQuery (coin : Bool) (first : Tag) : Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (by change Native.code[30]? = some .call; decide_cbv) rfl 12 (Native.returned 16 coin none first) (Native.second_setup_checked coin first)

theorem secondQuery_bound (coin : Bool) (first : Tag) :
    (secondQuery oracle callerOracle ret callerState trace coin first).budget () ≤ 146 * ret.table.length + 266 := by
  have bound := prefixed_bound oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (by change Native.code[30]? = some .call; decide_cbv) rfl 12 (Native.returned 16 coin none first) (Native.second_setup_checked coin first)
  apply le_trans bound
  omega

theorem secondQuery_growth (coin : Bool) (first : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((secondQuery oracle callerOracle ret callerState trace coin first).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth oracle callerOracle ret (Native.secondCall coin first) callerState trace (secondMessage first) [] (Native.residue first) rfl (by change Native.code[30]? = some .call; decide_cbv) rfl 12 (Native.returned 16 coin none first) (Native.second_setup_checked coin first) output supported

noncomputable def repeatedQuery (coin : Bool) (second : Tag) : Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed oracle callerOracle ret (Native.thirdCall coin second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (by change Native.code[119]? = some .call; decide_cbv) rfl 70 (Native.returned 31 coin none second) (repeated_checked coin second)

theorem repeatedQuery_bound (coin : Bool) (second : Tag) :
    (repeatedQuery oracle callerOracle ret callerState trace coin second).budget () ≤ 146 * ret.table.length + 324 := by
  have bound := prefixed_bound oracle callerOracle ret (Native.thirdCall coin second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (by change Native.code[119]? = some .call; decide_cbv) rfl 70 (Native.returned 31 coin none second) (repeated_checked coin second)
  apply le_trans bound
  omega

theorem repeatedQuery_growth (coin : Bool) (second : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((repeatedQuery oracle callerOracle ret callerState trace coin second).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth oracle callerOracle ret (Native.thirdCall coin second) callerState trace (firstMessage coin) [] (Native.residue second) rfl (by change Native.code[119]? = some .call; decide_cbv) rfl 70 (Native.returned 31 coin none second) (repeated_checked coin second) output supported

noncomputable def verifyQuery (coin : Bool) (second repeated : Tag) : Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  prefixed oracle callerOracle ret (Native.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (by change Native.code[205]? = some .call; decide_cbv) rfl ((if coin then 59 else 1) + 10) (Native.returned 120 coin (some second) repeated) (verify_checked coin second repeated)

theorem verifyQuery_bound (coin : Bool) (second repeated : Tag) :
    (verifyQuery oracle callerOracle ret callerState trace coin second repeated).budget () ≤ 146 * ret.table.length + 323 := by
  have bound := prefixed_bound oracle callerOracle ret (Native.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (by change Native.code[205]? = some .call; decide_cbv) rfl ((if coin then 59 else 1) + 10) (Native.returned 120 coin (some second) repeated) (verify_checked coin second repeated)
  apply le_trans bound
  cases coin <;> simp only [Bool.false_eq_true, if_false, if_true] at bound ⊢ <;> omega

theorem verifyQuery_growth (coin : Bool) (second repeated : Tag) (output : Retained State × Tag)
    (supported : output ∈ ((verifyQuery oracle callerOracle ret callerState trace coin second repeated).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 :=
  prefixed_growth oracle callerOracle ret (Native.lastCall coin (if coin then repeated else second) repeated) callerState trace (7) [] (Native.residue repeated) rfl (by change Native.code[205]? = some .call; decide_cbv) rfl ((if coin then 59 else 1) + 10) (Native.returned 120 coin (some second) repeated) (verify_checked coin second repeated) output supported

noncomputable def last (coin : Bool) (second repeated : Tag) :
    Procedure (step oracle callerOracle) Unit (Output State Source) :=
  follow oracle callerOracle (verifyQuery oracle callerOracle ret callerState trace coin second repeated)
    (fun answer => finish oracle callerOracle answer.1 callerState (Native.extendTrace 7 answer.2 trace)
      coin (if coin then repeated else second) answer.2)
    (fun _ _ => rfl) 35 (fun _ _ => finish_bound ..) (fun _ _ => rfl)

theorem last_bound (coin : Bool) (second repeated : Tag) :
    (last oracle callerOracle ret callerState trace coin second repeated).budget () ≤ 146 * ret.table.length + 358 := by
  change (verifyQuery oracle callerOracle ret callerState trace coin second repeated).budget () + 35 ≤ _
  have bound := verifyQuery_bound oracle callerOracle ret callerState trace coin second repeated
  omega

noncomputable def repeatedStage (coin : Bool) (second : Tag) :
    Procedure (step oracle callerOracle) Unit (Output State Source) :=
  follow oracle callerOracle (repeatedQuery oracle callerOracle ret callerState trace coin second)
    (fun answer => last oracle callerOracle answer.1 callerState
      (Native.extendTrace (firstMessage coin) answer.2 trace) coin second answer.2)
    (fun _ _ => rfl) (146 * (ret.table.length + 1) + 358) (by
      intro answer supported
      have bound := last_bound oracle callerOracle answer.1 callerState
        (Native.extendTrace (firstMessage coin) answer.2 trace) coin second answer.2
      have growth := repeatedQuery_growth oracle callerOracle ret callerState trace coin second answer supported
      omega) (fun _ _ => rfl)

theorem repeat_bound (coin : Bool) (second : Tag) :
    (repeatedStage oracle callerOracle ret callerState trace coin second).budget () ≤ 292 * ret.table.length + 828 := by
  change (repeatedQuery oracle callerOracle ret callerState trace coin second).budget () +
    (146 * (ret.table.length + 1) + 358) ≤ _
  have bound := repeatedQuery_bound oracle callerOracle ret callerState trace coin second
  omega

noncomputable def second (coin : Bool) (first : Tag) :
    Procedure (step oracle callerOracle) Unit (Output State Source) :=
  follow oracle callerOracle (secondQuery oracle callerOracle ret callerState trace coin first)
    (fun answer => repeatedStage oracle callerOracle answer.1 callerState
      (Native.extendTrace (secondMessage first) answer.2 trace) coin answer.2)
    (fun _ _ => rfl) (292 * (ret.table.length + 1) + 828) (by
      intro answer supported
      have bound := repeat_bound oracle callerOracle answer.1 callerState
        (Native.extendTrace (secondMessage first) answer.2 trace) coin answer.2
      have growth := secondQuery_growth oracle callerOracle ret callerState trace coin first answer supported
      omega) (fun _ _ => rfl)

theorem second_bound (coin : Bool) (first : Tag) :
    (second oracle callerOracle ret callerState trace coin first).budget () ≤ 438 * ret.table.length + 1386 := by
  change (secondQuery oracle callerOracle ret callerState trace coin first).budget () +
    (292 * (ret.table.length + 1) + 828) ≤ _
  have bound := secondQuery_bound oracle callerOracle ret callerState trace coin first
  omega

noncomputable def first (coin : Bool) : Procedure (step oracle callerOracle) Unit (Output State Source) :=
  follow oracle callerOracle (firstQuery oracle callerOracle ret callerState trace coin)
    (fun answer => second oracle callerOracle answer.1 callerState
      (Native.extendTrace (firstMessage coin) answer.2 trace) coin answer.2)
    (fun _ _ => rfl) (438 * (ret.table.length + 1) + 1386) (by
      intro answer supported
      have bound := second_bound oracle callerOracle answer.1 callerState
        (Native.extendTrace (firstMessage coin) answer.2 trace) coin answer.2
      have growth := firstQuery_growth oracle callerOracle ret callerState trace coin answer supported
      omega) (fun _ _ => rfl)

theorem first_bound (coin : Bool) :
    (first oracle callerOracle ret callerState trace coin).budget () ≤ 584 * ret.table.length + 2090 := by
  change (firstQuery oracle callerOracle ret callerState trace coin).budget () +
    (438 * (ret.table.length + 1) + 1386) ≤ _
  have bound := firstQuery_bound oracle callerOracle ret callerState trace coin
  omega

noncomputable def coin : Procedure (step oracle callerOracle) Unit Bool :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .running {}, trace⟩)
    (fun _ coin => .source ret.saved ⟨callerState, .running (Native.afterCoin coin), trace⟩)
    (fun _ => sampleBit) (fun _ => 1) (by
      intro _
      simp only [TimedExecution.eval, PMF.bind_pure]
      change (Reification.timedStep Native.code callerOracle ⟨callerState, .running {}, trace⟩).map
        (PacketResponseSource.Control.source ret.saved) = _
      rw [Native.initial_step, PMF.map_comp]
      rfl)

noncomputable def whole : Procedure (step oracle callerOracle) Unit (Output State Source) :=
  follow oracle callerOracle (coin oracle callerOracle ret callerState trace)
    (first oracle callerOracle ret callerState trace) (fun _ _ => rfl)
    (584 * ret.table.length + 2090) (fun _ _ => first_bound ..) (fun _ _ => rfl)

theorem whole_budget : (whole oracle callerOracle ret callerState trace).budget () = 584 * ret.table.length + 2091 := by
  change 1 + (584 * ret.table.length + 2090) = _
  omega

end Foundation.Hash.Native.CompactMACExecution
