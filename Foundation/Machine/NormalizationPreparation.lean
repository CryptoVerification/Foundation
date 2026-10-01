import Foundation.Machine.NormalizationInput

namespace Machine

/-- Continue from the physical end of a guarded choose result. Rewind the
raw response, cross its reserved separator with an actual move, rewind the
saved DDH input, and assemble the normalizer input on the opposite tape.
The source-call scratch prefix remains stored beyond its blank separator. -/
def prepareChooseNormalization : Program :=
  rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input] ++
    rewindBitstring.asSubroutine 6 11 ++
    prepareNormalizationInput.asSubroutine 11 93 ++ [.halt]

def prepareChooseNormalizationStart (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) : Configuration :=
  { inputTape := {
      left := reply.reverse.map some ++ none ::
        ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none])
      right := List.replicate blanks none },
    outputTape := { left := savedOutput } }

def prepareChooseNormalizationFinish (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) : Configuration :=
  { prepareNormalizationInputFinish [] savedOutput n instanceBits bit tupleTail reply blanks with pc := 93 }

def prepareChooseNormalizationSteps (n : Nat) (instanceBits tuple reply : List Bool) : Nat :=
  (2 * reply.length + 4) + 1 +
    (2 * (encodeSecurityParameter n ++ frame instanceBits ++ frame tuple).length + 4) +
    prepareNormalizationInputSteps n instanceBits tuple reply + 1

/-- This starts on a returned source configuration, not a newly loaded
request. All old input cells and response cells are retained. -/
theorem prepareChooseNormalization_runs (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) :
    RunsFor prepareChooseNormalization
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareChooseNormalizationSteps n instanceBits (bit :: tupleTail) reply) := by
  let ddhBits := encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)
  let savedDDH := ddhBits.reverse.map some ++ [none]
  let output : Tape := { left := savedOutput }
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({
        left := savedDDH
        right := reply.map some ++ none :: List.replicate blanks none } : Tape).moveRight,
      outputTape := output, halted := true }
  let back : Configuration :=
    { pc := 6,
      inputTape := {
        left := savedDDH
        right := reply.map some ++ none :: List.replicate blanks none },
      outputTape := output }
  let inputRewound : Configuration :=
    { pc := 3,
      inputTape := ({ right := ddhBits.map some ++ none ::
        (reply.map some ++ none :: List.replicate blanks none) } : Tape).moveRight,
      outputTape := output, halted := true }
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let assembled := prepareNormalizationInput.asSubroutine 11 93
  have hReply := (rewindScratch_runs_from savedDDH reply none (List.replicate blanks none) output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ assembled ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization
    (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
    (rewound.resumeAt 5) (2 * reply.length + 4) at hReply
  have hBack : Step prepareChooseNormalization (rewound.resumeAt 5) back := by
    cases reply <;> simp [Step, successors, next, prepareChooseNormalization,
      rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, rewound, back,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.moveLeft]
  have hDDH := (rewindScratch_runs_from [] ddhBits none
      (reply.map some ++ none :: List.replicate blanks none) output).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring (assembled ++ [.halt]) 11
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization back (inputRewound.resumeAt 11)
    (2 * ddhBits.length + 4) at hDDH
  have hStart : inputRewound.resumeAt 11 =
      (prepareNormalizationInputStart [] savedOutput n instanceBits bit tupleTail reply blanks).rebasePc 11 := by
    rw [prepareNormalizationInputStart_layout]
    simp [inputRewound, ddhBits, output, encodeSecurityParameter, frame,
      Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight, List.map_append,
      List.append_assoc]
    cases n <;> simp [List.replicate_succ]
  rw [hStart] at hDDH
  have hAssemble := (prepareNormalizationInput_runs [] savedOutput n instanceBits bit tupleTail reply blanks).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b) prepareNormalizationInput [.halt] 93
    (by change 0 < 81; decide) rfl rfl prepareNormalizationInput_control_closed
  change RunsFor prepareChooseNormalization
    ((prepareNormalizationInputStart [] savedOutput n instanceBits bit tupleTail reply blanks).rebasePc 11)
    ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 93)
    (prepareNormalizationInputSteps n instanceBits (bit :: tupleTail) reply) at hAssemble
  have hHalt : Step prepareChooseNormalization
      ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 93)
      (prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks) := by
    simp [Step, successors, next, prepareChooseNormalization, rewindBitstring,
      prepareNormalizationInput, preparePublicPrefixContext, skipUnary, skipFrame,
      savePublicPrefix, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
      copyBitstring, Program.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      prepareChooseNormalizationFinish, prepareNormalizationInputFinish, Configuration.resumeAt,
      Instruction.next]
  simpa only [prepareChooseNormalizationSteps, ddhBits, Nat.add_assoc] using
    RunsFor.succ (((RunsFor.succ hReply hBack).trans hDDH).trans hAssemble) hHalt

theorem prepareChooseNormalization_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareChooseNormalization := by
  simp [prepareChooseNormalization, prepareNormalizationInput, preparePublicPrefixContext,
    skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
    writeFrame, writeFrameHeader, rewindBitstring, copyBitstring, Program.swapTapes,
    Instruction.swapTapes, TapeId.swap, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareChooseNormalization_eval (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) :
    evalConfigWithin prepareChooseNormalization
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareChooseNormalizationSteps n instanceBits (bit :: tupleTail) reply) =
      PMF.pure (prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks) :=
  (prepareChooseNormalization_runs savedOutput n instanceBits bit tupleTail reply blanks).evalConfigWithin_eq_pure_of_no_randomBit
    prepareChooseNormalization_no_randomBit

theorem prepareChooseNormalizationSteps_le (n : Nat) (instanceBits tuple reply : List Bool) :
    prepareChooseNormalizationSteps n instanceBits tuple reply ≤
      50 * ((encodeSecurityParameter n ++ frame instanceBits ++ frame tuple).length + reply.length + 1) + 30 := by
  have h := prepareNormalizationInputSteps_le n instanceBits tuple reply
  simp only [prepareChooseNormalizationSteps]
  omega

set_option maxHeartbeats 2000000 in
theorem prepareChooseNormalization_control_closed (c d : Configuration)
    (hPc : c.pc < prepareChooseNormalization.length) (step : Step prepareChooseNormalization c d)
    (_hRunning : d.halted = false) : d.pc < prepareChooseNormalization.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 94 at hPc
  change d.pc < 94
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareChooseNormalization,
    prepareNormalizationInput, preparePublicPrefixContext, skipUnary, skipFrame,
    savePublicPrefix, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
    rewindBitstring, copyBitstring, Program.swapTapes, Instruction.swapTapes, TapeId.swap,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Both retained-input rewinds and request assembly stop on arbitrary
finite input tapes, including malformed choose continuations. The result
contains a contiguous finite normalizer request. A guarded call still needs
the caller-specific invariant on the other tape's blank frontier. -/
theorem prepareChooseNormalization_terminates_with_request_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used request saved,
      used ≤ 200000000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 200000000 ∧
      RunsFor prepareChooseNormalization
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape.Equivalent { Tape.ofBits request with left := none :: saved } ∧
      request.length ≤ finish.outputTape.cells := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨first, firstTime, hFirstTime, hFirstRun, hFirstHalt, hFirstOutput⟩ :=
    rewindBitstring_terminates_from input output
  obtain ⟨second, secondTime, hSecondTime, hSecondRun, hSecondHalt, hSecondOutput⟩ :=
    rewindBitstring_terminates_from first.inputTape.moveLeft first.outputTape
  obtain ⟨assembled, assemblyTime, request, saved, hAssemblyTime, hAssemblyRun,
    hAssemblyHalt, hRequest, hRequestLength⟩ :=
    prepareNormalizationInput_terminates_with_request_layout second.inputTape savedOutput blanks
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := prepareNormalizationInput.asSubroutine 11 93
  have hFirst := hFirstRun.withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl hFirstHalt rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization
    ({ inputTape := input, outputTape := output } : Configuration) (first.resumeAt 5) firstTime at hFirst
  let backed : Configuration := { pc := 6, inputTape := first.inputTape.moveLeft, outputTape := first.outputTape }
  have hBack : Step prepareChooseNormalization (first.resumeAt 5) backed := by
    simp [Step, successors, next, prepareChooseNormalization, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, backed,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSecond := hSecondRun.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring (k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl hSecondHalt rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization backed (second.resumeAt 11) secondTime at hSecond
  have hAssemblyEntry :
      ({ inputTape := second.inputTape, outputTape := output } : Configuration).rebasePc 11 =
      second.resumeAt 11 := by
    simp only [Configuration.rebasePc, Configuration.resumeAt, hSecondOutput, hFirstOutput, Nat.add_zero]
  have hAssembly := hAssemblyRun.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b) prepareNormalizationInput [.halt] 93
    (by change 0 < 81; decide) rfl hAssemblyHalt prepareNormalizationInput_control_closed
  change RunsFor prepareChooseNormalization
    (({ inputTape := second.inputTape, outputTape := output } : Configuration).rebasePc 11)
    (assembled.resumeAt 93) assemblyTime at hAssembly
  rw [hAssemblyEntry] at hAssembly
  let finish : Configuration := { assembled with pc := 93, halted := true }
  have hHalt : Step prepareChooseNormalization (assembled.resumeAt 93) finish := by
    simp [Step, successors, next, prepareChooseNormalization, rewindBitstring,
      prepareNormalizationInput, preparePublicPrefixContext, skipUnary, skipFrame,
      savePublicPrefix, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
      copyBitstring, Program.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, finish, Instruction.next]
  have hUntilSecond := (RunsFor.succ hFirst hBack).trans hSecond
  refine ⟨finish, firstTime + 1 + secondTime + assemblyTime + 1, request, saved,
    ?_, RunsFor.succ (hUntilSecond.trans hAssembly) hHalt, rfl, hRequest, hRequestLength⟩
  have hFirstStorage := GuardedCompiler.sourceStorage_le_of_run hFirst
  have hSecondStorage := GuardedCompiler.sourceStorage_le_of_run hUntilSecond
  simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hFirstStorage hSecondStorage
  have hInitialLeft : input.left.length ≤ input.cells := by dsimp only [Tape.cells]; omega
  have hMovedCells := Tape.cells_moveLeft_le first.inputTape
  have hMovedLeft : first.inputTape.moveLeft.left.length ≤ first.inputTape.moveLeft.cells := by
    dsimp only [Tape.cells]; omega
  change assemblyTime ≤ 5000000 * (second.inputTape.cells + output.cells) + 5000000 at hAssemblyTime
  change _ ≤ 200000000 * (input.cells + output.cells) + 200000000
  omega

/-- Every finite raw choose reply is separated from the retained caller
cells by an actual blank. Rewinding those cells and assembling the request
therefore gives both guarded-call tapes, even for a malformed reply or a
malformed saved DDH prefix. No validity decoder is assumed here. -/
theorem prepareChooseNormalization_terminates_with_guarded_layout
    (beforeInput savedOutput : List (Option Bool)) (reply : List Bool)
    (inputBlanks outputBlanks : Nat) :
    ∃ finish used sourceSaved targetSaved request,
      used ≤ 200000000 *
        (({ left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 200000000 ∧
      RunsFor prepareChooseNormalization
        ({ inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
           outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart sourceSaved targetSaved request).swapTapes ∧
      request.length ≤ finish.outputTape.cells := by
  let input : Tape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none }
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := beforeInput, right := reply.map some ++ none :: List.replicate inputBlanks none } : Tape).moveRight,
      outputTape := output, halted := true }
  let backed : Configuration :=
    { pc := 6, inputTape := { left := beforeInput, right := reply.map some ++ none :: List.replicate inputBlanks none }, outputTape := output }
  obtain ⟨second, leading, before, _hLeadingLength, hSecondRun, hSecondHalt, hSecondInput, hSecondOutput⟩ :=
    rewindBitstring_terminates_with_layout backed.inputTape output
  have hBlocks : ∃ first trailing : List Bool, ∃ padding : Nat,
      second.inputTape.right = first.map some ++ none ::
        (trailing.map some ++ List.replicate padding none) := by
    rw [hSecondInput]
    cases leading with
    | nil => exact ⟨reply, [], inputBlanks, rfl⟩
    | cons bit rest =>
        refine ⟨rest, reply, inputBlanks + 1, ?_⟩
        simp [backed, List.map_cons, Tape.moveRight, List.replicate_succ]
  obtain ⟨first, trailing, padding, hRight⟩ := hBlocks
  obtain ⟨assembled, assemblyTime, sourceSaved, targetSaved, request, _hAssemblyTime,
    hAssemblyRun, hAssemblyHalt, hLayout, hRequestLength⟩ :=
    prepareNormalizationInput_terminates_with_guarded_layout second.inputTape savedOutput outputBlanks
      first trailing padding hRight
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := prepareNormalizationInput.asSubroutine 11 93
  have hFirst := (rewindScratch_runs_from beforeInput reply none (List.replicate inputBlanks none) output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization
    ({ inputTape := input, outputTape := output } : Configuration) (rewound.resumeAt 5)
    (2 * reply.length + 4) at hFirst
  have hBack : Step prepareChooseNormalization (rewound.resumeAt 5) backed := by
    cases reply <;> simp [Step, successors, next, prepareChooseNormalization,
      rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, rewound, backed,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.moveLeft]
  have hSecond := hSecondRun.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring (k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl hSecondHalt rewindBitstring_control_closed
  change RunsFor prepareChooseNormalization backed (second.resumeAt 11) (2 * leading.length + 4) at hSecond
  have hAssemblyEntry :
      ({ inputTape := second.inputTape, outputTape := output } : Configuration).rebasePc 11 =
      second.resumeAt 11 := by
    simp only [Configuration.rebasePc, Configuration.resumeAt, hSecondOutput, Nat.add_zero]
  have hAssembly := hAssemblyRun.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b) prepareNormalizationInput [.halt] 93
    (by change 0 < 81; decide) rfl hAssemblyHalt prepareNormalizationInput_control_closed
  change RunsFor prepareChooseNormalization
    (({ inputTape := second.inputTape, outputTape := output } : Configuration).rebasePc 11)
    (assembled.resumeAt 93) assemblyTime at hAssembly
  rw [hAssemblyEntry] at hAssembly
  let nativeFinish : Configuration := { assembled with pc := 93, halted := true }
  have hHalt : Step prepareChooseNormalization (assembled.resumeAt 93) nativeFinish := by
    simp [Step, successors, next, prepareChooseNormalization, rewindBitstring,
      prepareNormalizationInput, preparePublicPrefixContext, skipUnary, skipFrame,
      savePublicPrefix, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
      copyBitstring, Program.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, nativeFinish, Instruction.next]
  have hNativeRun : RunsFor prepareChooseNormalization
      ({ inputTape := input, outputTape := output } : Configuration) nativeFinish
      ((2 * reply.length + 4) + 1 + (2 * leading.length + 4) + assemblyTime + 1) :=
    RunsFor.succ (((RunsFor.succ hFirst hBack).trans hSecond).trans hAssembly) hHalt
  obtain ⟨finish, used, _oldRequest, _oldSaved, hBound, hRun, hHalted, _hOldRequest, _hOldLength⟩ :=
    prepareChooseNormalization_terminates_with_request_layout input savedOutput outputBlanks
  have hSame : finish = nativeFinish := hRun.halted_finish_eq_of_no_randomBit
    hNativeRun hHalted rfl prepareChooseNormalization_no_randomBit
  have hActualLayout : (finish.resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart sourceSaved targetSaved request).swapTapes := by
    rw [hSame]
    exact hLayout
  exact ⟨finish, used, sourceSaved, targetSaved, request,
    hBound, hRun, hHalted, hActualLayout, hActualLayout.2.2.2.contiguous_length_le_cells⟩

end Machine
