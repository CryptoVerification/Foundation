import Foundation.Crypto.Semantics.Machine.MessageSelection
import Foundation.Crypto.Semantics.Machine.BitstringRewind
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine

open Foundation.Probability

/-- Canonical response layout only. Encoding it is not a machine opcode:
these bits must already have been written by the certified normalizer. -/
def canonicalMessageBits (first second state : List Bool) : List Bool :=
  false :: (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ state)

/-- Native continuation from the end of a canonical normalization result.
Rewind the unchanged response, sample a fair challenge, position the selected
message field, and halt. Saved DDH/raw-response cells and normalizer scratch
are retained on their respective tapes. -/
def prepareMessageSelection : Program :=
  let pre := rewindBitstring.asSubroutine 0 5
  Program.withSubroutine pre selectMessage [.halt] (pre.length + selectMessage.length + 1)

def prepareMessageSelectionStart (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := {
      left := (canonicalMessageBits first second state).reverse.map some ++ none :: beforeInput
      right := List.replicate blanks none },
    outputTape := { left := beforeOutput } }

def prepareMessageSelectionFinish (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) : Configuration :=
  { selectMessageFinish (none :: beforeInput) beforeOutput first second
      (state.map some ++ none :: List.replicate blanks none) bit with pc := 23 }

def prepareMessageSelectionSteps (first second state : List Bool) : Nat :=
  (2 * (canonicalMessageBits first second state).length + 4) + (4 * first.length + 9) + 1

private theorem selectionPreparation_layout :
    prepareMessageSelection = Program.withSubroutine [] rewindBitstring
      (selectMessage.asSubroutine 5 23 ++ [.halt]) 5 := rfl

/-- Full configuration law from stored normalized cells. The same bit
chosen by the native random instruction remains saved on the output tape
and determines the input field selected for the group-operation request. -/
theorem prepareMessageSelection_eval (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) :
    evalConfigWithin prepareMessageSelection
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      (prepareMessageSelectionSteps first second state) =
      sampleBit.map (prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks) := by
  let pre := rewindBitstring.asSubroutine 0 5
  let output : Tape := { left := beforeOutput }
  let start := selectMessageStart (none :: beforeInput) beforeOutput first second
    (state.map some ++ none :: List.replicate blanks none)
  have hRewind := (rewindScratch_runs_from beforeInput (canonicalMessageBits first second state)
      none (List.replicate blanks none) output).evalConfigWithin_withSubroutine_halted_of_closed
    [] rewindBitstring (selectMessage.asSubroutine 5 23 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed rewindBitstring_no_randomBit
  rw [← selectionPreparation_layout] at hRewind
  have hRewind' : evalConfigWithin prepareMessageSelection
    (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
    (2 * (canonicalMessageBits first second state).length + 4) =
      PMF.pure (start.rebasePc 5) := by
    simpa [prepareMessageSelectionStart, start, selectMessageStart, output,
      canonicalMessageBits, Tape.moveRight, Configuration.resumeAt, Configuration.rebasePc,
      List.map_append, List.append_assoc] using hRewind
  have hSelection := Program.evalConfigWithin_withSubroutine_final_halt pre selectMessage start
    (by change 0 ≤ 17; decide) rfl (4 * first.length + 9)
    (selectMessage_haltsFrom (none :: beforeInput) beforeOutput first second
      (state.map some ++ none :: List.replicate blanks none))
  change evalConfigWithin prepareMessageSelection (start.rebasePc 5)
    ((4 * first.length + 9) + 1) =
      (evalConfigWithin selectMessage start (4 * first.length + 9)).map
        (fun c => { c with pc := 23, halted := true }) at hSelection
  rw [prepareMessageSelectionSteps, Nat.add_assoc, evalConfigWithin_add, hRewind',
    PMF.pure_bind, hSelection]
  change (evalConfigWithin selectMessage
    (selectMessageStart (none :: beforeInput) beforeOutput first second
      (state.map some ++ none :: List.replicate blanks none))
    (4 * first.length + 9)).map _ = _
  rw [selectMessage_eval, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> rfl

theorem prepareMessageSelection_haltsFrom (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareMessageSelection
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      finish (prepareMessageSelectionSteps first second state)) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareMessageSelection_eval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _hBit, rfl⟩ := hMem
  cases bit <;> rfl

theorem prepareMessageSelection_steps_le (first second state : List Bool) :
    prepareMessageSelectionSteps first second state ≤
      6 * (canonicalMessageBits first second state).length + 14 := by
  have hLength : first.length ≤ (canonicalMessageBits first second state).length := by
    simp [canonicalMessageBits, FiniteBitEncoding.delimit_length]
    omega
  simp only [prepareMessageSelectionSteps]
  omega

theorem prepareMessageSelectionFinish_output (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) :
    (prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).outputTape =
      { left := none :: some bit :: beforeOutput } :=
  selectMessageFinish_output _ _ _ _ _ _

/-- Complete two-branch distribution for native rewind and selection on
arbitrary finite tapes. Output storage depends only on the one native fair
bit and two charged head moves, even when input fields are malformed. -/
theorem prepareMessageSelection_eval_with_input_layout (input output : Tape) :
    ∃ finish : Bool → Configuration,
      evalConfigWithin prepareMessageSelection
        ({ inputTape := input, outputTape := output } : Configuration)
        (40 * (input.cells + output.cells) + 50) = Foundation.Probability.sampleBit.map finish ∧
      ∀ bit, (finish bit).halted = true ∧
        (finish bit).outputTape = (output.write (some bit)).moveRight.moveRight ∧
        ∀ (raw : List Bool) (blanks : Nat),
          input.current :: input.right = raw.map some ++ none :: List.replicate blanks none →
          ∃ (remaining : List Bool) (padding : Nat),
            (finish bit).inputTape.current :: (finish bit).inputTape.right =
              remaining.map some ++ none :: List.replicate padding none := by
  obtain ⟨rewound, leading, _saved, hLeading, hRewindRun, hRewindHalt, hRewindInput, hRewindOutput⟩ :=
    rewindBitstring_terminates_with_layout input output
  let rewindTime := 2 * leading.length + 4
  have hRewindTime : rewindTime ≤ 2 * input.left.length + 4 := by dsimp only [rewindTime]; omega
  let pre := rewindBitstring.asSubroutine 0 5
  let start := rewound.resumeAt 0
  let selectionTime := 4 * rewound.inputTape.cells + 21
  have hSelection (target : Configuration) (trace : PaddedRunsFor selectMessage start target selectionTime) :
      target.halted = true := by
    change PaddedRunsFor selectMessage
      ({ inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration)
      target (4 * rewound.inputTape.cells + 21) at trace
    exact selectMessage_haltsFrom_anyTape _ _ _ trace
  have hRewind := hRewindRun.evalConfigWithin_withSubroutine_halted_of_closed
    [] rewindBitstring (selectMessage.asSubroutine 5 23 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed rewindBitstring_no_randomBit
  rw [← selectionPreparation_layout] at hRewind
  change evalConfigWithin prepareMessageSelection
    ({ inputTape := input, outputTape := output } : Configuration) rewindTime =
    PMF.pure (rewound.resumeAt 5) at hRewind
  have hSelect := Program.evalConfigWithin_withSubroutine_final_halt pre selectMessage start
    (by change 0 ≤ 17; decide) rfl selectionTime hSelection
  change evalConfigWithin prepareMessageSelection (rewound.resumeAt 5) (selectionTime + 1) =
    (evalConfigWithin selectMessage start selectionTime).map
      (fun c => { c with pc := 23, halted := true }) at hSelect
  obtain ⟨selected, hSelected, hSelectedFinish⟩ :=
    selectMessage_eval_anyTape rewound.inputTape rewound.outputTape
  change evalConfigWithin selectMessage start selectionTime =
    Foundation.Probability.sampleBit.map selected at hSelected
  have hLaw : evalConfigWithin prepareMessageSelection
      ({ inputTape := input, outputTape := output } : Configuration)
      (rewindTime + (selectionTime + 1)) =
      Foundation.Probability.sampleBit.map (fun bit => { selected bit with pc := 23, halted := true }) := by
    rw [evalConfigWithin_add, hRewind, PMF.pure_bind, hSelect, hSelected, PMF.map_comp]
    rfl
  have hAt (target : Configuration)
      (trace : PaddedRunsFor prepareMessageSelection
        ({ inputTape := input, outputTape := output } : Configuration) target
        (rewindTime + (selectionTime + 1))) : target.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hLaw, PMF.mem_support_map_iff] at hMem
    obtain ⟨bit, _hBit, rfl⟩ := hMem
    rfl
  have hStorage := GuardedCompiler.sourceStorage_le_of_run hRewindRun
  simp only [GuardedCompiler.sourceStorage] at hStorage
  have hLeft : input.left.length ≤ input.cells := by dsimp only [Tape.cells]; omega
  have hBound : rewindTime + (selectionTime + 1) ≤ 40 * (input.cells + output.cells) + 50 := by
    dsimp only [selectionTime]
    omega
  refine ⟨fun bit => { selected bit with pc := 23, halted := true }, ?_, ?_⟩
  · rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hLaw]
  · intro bit
    refine ⟨rfl, (hSelectedFinish bit).2.trans
      (congrArg (fun tape : Tape => (tape.write (some bit)).moveRight.moveRight) hRewindOutput), ?_⟩
    intro raw blanks hForward
    have hRewoundForward : rewound.inputTape.current :: rewound.inputTape.right =
        (leading ++ raw).map some ++ none :: List.replicate blanks none := by
      rw [hRewindInput]
      cases leading <;> cases raw <;> simp [Tape.moveRight, List.cons_append, List.map_append, hForward]
    have hMem : selected bit ∈ (evalConfigWithin selectMessage start selectionTime).support := by
      rw [hSelected, PMF.mem_support_map_iff]
      exact ⟨bit, by simp [Foundation.Probability.sampleBit, Foundation.Probability.uniform], rfl⟩
    obtain ⟨moves, _hMoves, hMoved⟩ := selectMessage_input_moveRight
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
    change ∃ (remaining : List Bool) (padding : Nat),
      (selected bit).inputTape.current :: (selected bit).inputTape.right =
        remaining.map some ++ none :: List.replicate padding none
    rw [hMoved]
    exact moveRight_iterate_raw_frontier rewound.inputTape (leading ++ raw) blanks moves hRewoundForward


/-- The original complete two-branch law remains available without the
additional raw-input frontier postcondition. -/
theorem prepareMessageSelection_eval_anyTape (input output : Tape) :
    ∃ finish : Bool → Configuration,
      evalConfigWithin prepareMessageSelection
        ({ inputTape := input, outputTape := output } : Configuration)
        (40 * (input.cells + output.cells) + 50) = Foundation.Probability.sampleBit.map finish ∧
      ∀ bit, (finish bit).halted = true ∧
        (finish bit).outputTape = (output.write (some bit)).moveRight.moveRight := by
  obtain ⟨finish, hEval, hFinish⟩ := prepareMessageSelection_eval_with_input_layout input output
  exact ⟨finish, hEval, fun bit => ⟨(hFinish bit).1, (hFinish bit).2.1⟩⟩

/-- Rewind and fair-bit message selection stop on arbitrary retained finite
tapes. Canonical normalized-response validity is not a premise. -/
theorem prepareMessageSelection_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor prepareMessageSelection
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (40 * (input.cells + output.cells) + 50)) : finish.halted = true := by
  obtain ⟨target, hEval, hFinish⟩ := prepareMessageSelection_eval_anyTape input output
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [hEval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _hBit, rfl⟩ := hMem
  exact (hFinish bit).1

end Machine
