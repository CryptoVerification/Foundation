import Foundation.Machine.ContextualFrame
import Foundation.Machine.ContextualInput
import Foundation.Machine.TapeSwap

namespace Machine

/-- Move from a saved public-input prefix back to the selected message,
copy that message into the other tape's fresh scratch region, and append its
frame to the public prefix. Tape operands are relabeled in finite syntax;
there is no instruction that swaps, copies, or resets an entire tape. -/
def frameSavedMessage : Program :=
  rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output] ++
  rewindBitstring.swapTapes.asSubroutine 7 12 ++
  copyBitstring.swapTapes.asSubroutine 12 21 ++ [.moveRight .output, .moveRight .output] ++
  GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++ [.moveLeft .output] ++
  rewindBitstring.asSubroutine 30 35 ++ writeFrame.asSubroutine 35 60 ++ [.halt]

private def savedMessageAt (before : List (Option Bool)) (bits : List Bool)
    (tail : List (Option Bool)) : Tape :=
  { ({ right := bits.map some ++ tail } : Tape).moveRight with left := before }

def frameSavedMessageStart (savedInput savedOutput : List (Option Bool))
    (publicBits message : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { left := none :: savedInput, right := List.replicate blanks none },
    outputTape := {
      left := publicBits.reverse.map some ++ none :: none ::
        message.reverse.map some ++ none :: savedOutput } }

def frameSavedMessageFinish (savedInput savedOutput : List (Option Bool))
    (publicBits message : List Bool) (blanks : Nat) : Configuration :=
  { pc := 60,
    inputTape := {
      left := message.reverse.map some ++ none :: savedInput
      right := List.replicate (blanks - message.length) none },
    outputTape := {
      left := (publicBits ++ frame message).reverse.map some ++
        none :: none :: message.reverse.map some ++ none :: savedOutput },
    halted := true }

def frameSavedMessageSteps (publicBits message : List Bool) : Nat :=
  (2 * publicBits.length + 4) + 2 + (2 * message.length + 4) +
    copyBitstringSteps message + 2 + (3 * publicBits.length + 3) + 1 +
    (2 * message.length + 4) + writeFrameSteps message + 1

set_option maxHeartbeats 800000 in
/-- Exact native execution on both physical tapes. The saved message and
caller data remain in place; only a new copy is used as framing scratch. -/
theorem frameSavedMessage_runs (savedInput savedOutput : List (Option Bool))
    (publicBits message : List Bool) (blanks : Nat) :
    RunsFor frameSavedMessage (frameSavedMessageStart savedInput savedOutput publicBits message blanks)
      (frameSavedMessageFinish savedInput savedOutput publicBits message blanks)
      (frameSavedMessageSteps publicBits message) := by
  let scratch : Tape := { left := none :: savedInput, right := List.replicate blanks none }
  let savedRegion := none :: none :: message.reverse.map some ++ none :: savedOutput
  let atPublic : Configuration :=
    { pc := 3, inputTape := scratch,
      outputTape := savedMessageAt savedRegion publicBits [none], halted := true }
  have hFirst := (rewindScratch_runs_from
      (none :: message.reverse.map some ++ none :: savedOutput) publicBits none [] scratch).swapTapes.withSubroutine_halted_of_closed
    [] rewindBitstring.swapTapes
    ([.moveLeft .output, .moveLeft .output] ++ rewindBitstring.swapTapes.asSubroutine 7 12 ++
      copyBitstring.swapTapes.asSubroutine 12 21 ++ [.moveRight .output, .moveRight .output] ++
      GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++ [.moveLeft .output] ++
      rewindBitstring.asSubroutine 30 35 ++ writeFrame.asSubroutine 35 60 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  have hFirstFinish : ({
      pc := 3
      inputTape := ({
        left := none :: message.reverse.map some ++ none :: savedOutput
        right := publicBits.map some ++ [none] } : Tape).moveRight
      outputTape := scratch
      halted := true } : Configuration).swapTapes = atPublic := by
    cases publicBits <;> simp [atPublic, savedMessageAt, savedRegion, Configuration.swapTapes, Tape.moveRight]
  rw [hFirstFinish] at hFirst
  have hFirst' : RunsFor frameSavedMessage
      (frameSavedMessageStart savedInput savedOutput publicBits message blanks)
      (atPublic.resumeAt 5) (2 * publicBits.length + 4) := by
    simpa [frameSavedMessage, Program.withSubroutine, frameSavedMessageStart,
      Configuration.swapTapes, Configuration.rebasePc, scratch, List.append_assoc] using hFirst
  let between : Configuration :=
    { pc := 6, inputTape := scratch,
      outputTape := {
        left := none :: message.reverse.map some ++ none :: savedOutput
        right := publicBits.map some ++ [none] } }
  let atMessageEnd : Configuration :=
    { pc := 7, inputTape := scratch,
      outputTape := {
        left := message.reverse.map some ++ none :: savedOutput
        right := none :: publicBits.map some ++ [none] } }
  have hLeft₁ : Step frameSavedMessage (atPublic.resumeAt 5) between := by
    cases publicBits <;> simp [Step, successors, next, frameSavedMessage, rewindBitstring,
      Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      atPublic, between, savedMessageAt, savedRegion, Configuration.resumeAt, Tape.moveRight,
      Tape.moveLeft, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hLeft₂ : Step frameSavedMessage between atMessageEnd := by
    simp [Step, successors, next, frameSavedMessage, rewindBitstring,
      Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      between, atMessageEnd, Tape.moveLeft, Instruction.next, Configuration.updateTape, Configuration.advance]
  let atMessage : Configuration :=
    { pc := 3, inputTape := scratch,
      outputTape := savedMessageAt (none :: savedOutput) message
        (none :: none :: publicBits.map some ++ [none]), halted := true }
  have hMessage := (rewindScratch_runs_from savedOutput message none
      (none :: publicBits.map some ++ [none]) scratch).swapTapes.withSubroutine_halted_of_closed
    (rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output])
    rewindBitstring.swapTapes
    (copyBitstring.swapTapes.asSubroutine 12 21 ++ [.moveRight .output, .moveRight .output] ++
      GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++ [.moveLeft .output] ++
      rewindBitstring.asSubroutine 30 35 ++ writeFrame.asSubroutine 35 60 ++ [.halt]) 12
    (by change 0 < 4; decide) rfl rfl
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  have hMessage' : RunsFor frameSavedMessage atMessageEnd (atMessage.resumeAt 12)
      (2 * message.length + 4) := by
    cases message <;> simpa [frameSavedMessage, Program.withSubroutine, Program.asSubroutine_length,
      rewindBitstring, Program.swapTapes_length, atMessageEnd, atMessage, savedMessageAt,
      Configuration.swapTapes, Configuration.rebasePc, Configuration.resumeAt,
      Tape.moveRight, List.append_assoc] using hMessage
  let copied := (copySegmentFinish (none :: savedOutput) (none :: savedInput)
    (none :: publicBits.map some ++ [none]) message blanks).swapTapes
  have hCopy := (copySegment_runs (none :: savedOutput) (none :: savedInput)
      (none :: publicBits.map some ++ [none]) message blanks).swapTapes.withSubroutine_halted_of_closed
    (rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output] ++
      rewindBitstring.swapTapes.asSubroutine 7 12) copyBitstring.swapTapes
    ([.moveRight .output, .moveRight .output] ++
      GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++ [.moveLeft .output] ++
      rewindBitstring.asSubroutine 30 35 ++ writeFrame.asSubroutine 35 60 ++ [.halt]) 21
    (by change 0 < 8; decide) rfl rfl
    (Program.controlClosed_swapTapes _ GuardedCompiler.copyBitstring_control_closed)
  have hCopyStart : ((copySegmentStart (none :: savedOutput) (none :: savedInput)
      (none :: publicBits.map some ++ [none]) message blanks).swapTapes).rebasePc 12 =
      atMessage.resumeAt 12 := by
    cases message <;> simp [copySegmentStart_layout, atMessage, savedMessageAt, scratch,
      Configuration.swapTapes, Configuration.rebasePc, Configuration.resumeAt, Tape.moveRight]
  change RunsFor frameSavedMessage
    (((copySegmentStart (none :: savedOutput) (none :: savedInput)
      (none :: publicBits.map some ++ [none]) message blanks).swapTapes).rebasePc 12)
    (copied.resumeAt 21) (copyBitstringSteps message) at hCopy
  rw [hCopyStart] at hCopy
  let atSecondBlank : Configuration :=
    { pc := 22, inputTape := copied.inputTape,
      outputTape := {
        left := none :: message.reverse.map some ++ none :: savedOutput
        right := publicBits.map some ++ [none] } }
  let restoredPublic := seekBitstringNextStart savedRegion publicBits [] copied.inputTape
  have hRight₁ : Step frameSavedMessage (copied.resumeAt 21) atSecondBlank := by
    simp [Step, successors, next, frameSavedMessage, rewindBitstring, copyBitstring,
      Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      copied, copySegmentFinish, Configuration.swapTapes, Configuration.resumeAt, atSecondBlank,
      Tape.moveRight, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRight₂ : Step frameSavedMessage atSecondBlank (restoredPublic.swapTapes.rebasePc 23) := by
    cases publicBits <;> simp [Step, successors, next, frameSavedMessage, rewindBitstring, copyBitstring,
      Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      atSecondBlank, restoredPublic, seekBitstringNextStart_layout, savedRegion,
      Configuration.swapTapes, Configuration.rebasePc, Tape.moveRight,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSeek := (seekBitstringNext_runs savedRegion publicBits [] copied.inputTape).swapTapes.withSubroutine_halted_of_closed
    (rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output] ++
      rewindBitstring.swapTapes.asSubroutine 7 12 ++ copyBitstring.swapTapes.asSubroutine 12 21 ++
      [.moveRight .output, .moveRight .output]) GuardedCompiler.seekScratchInput.swapTapes
    ([.moveLeft .output] ++ rewindBitstring.asSubroutine 30 35 ++ writeFrame.asSubroutine 35 60 ++ [.halt]) 29
    (by change 0 < 5; decide) rfl rfl
    (Program.controlClosed_swapTapes _ GuardedCompiler.seekScratchInput_control_closed)
  let afterPublic := (seekBitstringNextFinish savedRegion publicBits [] copied.inputTape).swapTapes
  change RunsFor frameSavedMessage (restoredPublic.swapTapes.rebasePc 23) (afterPublic.resumeAt 29)
    (3 * publicBits.length + 3) at hSeek
  let atArgumentEnd : Configuration :=
    { pc := 30, inputTape := copied.inputTape,
      outputTape := { left := publicBits.reverse.map some ++ savedRegion, right := [none] } }
  have hBack : Step frameSavedMessage (afterPublic.resumeAt 29) atArgumentEnd := by
    simp [Step, successors, next, frameSavedMessage, rewindBitstring, copyBitstring,
      GuardedCompiler.seekScratchInput, Program.swapTapes, Instruction.swapTapes,
      Program.asSubroutine, Instruction.asSubroutine, afterPublic, seekBitstringNextFinish_layout_cells,
      Configuration.swapTapes, Configuration.resumeAt, atArgumentEnd, Tape.moveRight,
      Tape.moveLeft, Instruction.next, Configuration.updateTape, Configuration.advance]
  let beforeOutput := publicBits.reverse.map some ++ savedRegion
  let frameStart := writeFrameContextPaddedStart savedInput beforeOutput
    (List.replicate (blanks - message.length) none) message 1
  have hRewind := (rewindScratch_runs_from savedInput message none
      (List.replicate (blanks - message.length) none) atArgumentEnd.outputTape).withSubroutine_halted_of_closed
    (rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output] ++
      rewindBitstring.swapTapes.asSubroutine 7 12 ++ copyBitstring.swapTapes.asSubroutine 12 21 ++
      [.moveRight .output, .moveRight .output] ++ GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++
      [.moveLeft .output]) rewindBitstring (writeFrame.asSubroutine 35 60 ++ [.halt]) 35
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hRewindFinish : ({
      pc := 3
      inputTape := ({
        left := savedInput
        right := message.map some ++ none :: List.replicate (blanks - message.length) none } : Tape).moveRight
      outputTape := atArgumentEnd.outputTape
      halted := true } : Configuration).resumeAt 35 = frameStart.rebasePc 35 := by
    cases message <;> simp [frameStart, writeFrameContextPaddedStart_layout, beforeOutput, atArgumentEnd,
      writeFrameContextPaddedStart_layout, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hRewindFinish] at hRewind
  change RunsFor frameSavedMessage atArgumentEnd (frameStart.rebasePc 35)
    (2 * message.length + 4) at hRewind
  have hFrame := (writeFrameContextPadded_runs savedInput beforeOutput
      (List.replicate (blanks - message.length) none) message 1).withSubroutine_halted_of_closed
    (rewindBitstring.swapTapes.asSubroutine 0 5 ++ [.moveLeft .output, .moveLeft .output] ++
      rewindBitstring.swapTapes.asSubroutine 7 12 ++ copyBitstring.swapTapes.asSubroutine 12 21 ++
      [.moveRight .output, .moveRight .output] ++ GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29 ++
      [.moveLeft .output] ++ rewindBitstring.asSubroutine 30 35)
    writeFrame [.halt] 60 (by change 0 < 24; decide) rfl rfl writeFrame_control_closed
  have hFrameFinish : writeFrameContextPaddedFinish savedInput beforeOutput
      (List.replicate (blanks - message.length) none) message 1 =
      { frameSavedMessageFinish savedInput savedOutput publicBits message blanks with pc := 23 } := by
    have hPadding : 1 - (2 * message.length + 1) = 0 := by omega
    simp [writeFrameContextPaddedFinish, frameSavedMessageFinish, beforeOutput, savedRegion,
      hPadding, List.reverse_append, List.map_append, List.append_assoc]
  rw [hFrameFinish] at hFrame
  change RunsFor frameSavedMessage (frameStart.rebasePc 35)
    ((frameSavedMessageFinish savedInput savedOutput publicBits message blanks).resumeAt 60)
    (writeFrameSteps message) at hFrame
  have hHalt : Step frameSavedMessage
      ((frameSavedMessageFinish savedInput savedOutput publicBits message blanks).resumeAt 60)
      (frameSavedMessageFinish savedInput savedOutput publicBits message blanks) := by
    simp [Step, successors, next, frameSavedMessage, rewindBitstring, copyBitstring,
      GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader, Program.swapTapes,
      Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      frameSavedMessageFinish, Configuration.resumeAt, Instruction.next]
  have hToMessage := (RunsFor.succ (RunsFor.succ hFirst' hLeft₁) hLeft₂).trans hMessage'
  have hToCopy := hToMessage.trans hCopy
  have hToPublic := (RunsFor.succ (RunsFor.succ hToCopy hRight₁) hRight₂).trans hSeek
  have hToFrame := (RunsFor.succ hToPublic hBack).trans hRewind
  have hToHalt := RunsFor.succ (hToFrame.trans hFrame) hHalt
  convert hToHalt using 1
  simp only [frameSavedMessageSteps]

theorem frameSavedMessage_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ frameSavedMessage := by
  simp [frameSavedMessage, rewindBitstring, copyBitstring, GuardedCompiler.seekScratchInput,
    writeFrame, writeFrameHeader, Program.swapTapes, Instruction.swapTapes,
    Program.asSubroutine, Instruction.asSubroutine]

theorem frameSavedMessage_eval (savedInput savedOutput : List (Option Bool))
    (publicBits message : List Bool) (blanks : Nat) :
    evalConfigWithin frameSavedMessage
      (frameSavedMessageStart savedInput savedOutput publicBits message blanks)
      (frameSavedMessageSteps publicBits message) =
      PMF.pure (frameSavedMessageFinish savedInput savedOutput publicBits message blanks) :=
  (frameSavedMessage_runs savedInput savedOutput publicBits message blanks).evalConfigWithin_eq_pure_of_no_randomBit
    frameSavedMessage_no_randomBit

theorem frameSavedMessage_steps_le (publicBits message : List Bool) :
    frameSavedMessageSteps publicBits message ≤ 5 * publicBits.length + 23 * message.length + 34 := by
  have hCopy := copyBitstringSteps_le message
  have hFrame := writeFrameSteps_le message
  simp only [frameSavedMessageSteps]
  omega

set_option maxHeartbeats 1000000 in
theorem frameSavedMessage_control_closed (c d : Configuration)
    (hPc : c.pc < frameSavedMessage.length) (step : Step frameSavedMessage c d)
    (_hRunning : d.halted = false) : d.pc < frameSavedMessage.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 61 at hPc
  change d.pc < 61
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, frameSavedMessage,
    rewindBitstring, copyBitstring, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
    Program.swapTapes, Instruction.swapTapes, TapeId.swap,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem savedMessage_seek_frontier (before : List (Option Bool))
    (publicBits : List Bool) (padding : Nat) (gap : Bool) (output : Tape) :
    let tail := if gap then none :: publicBits.map some ++ none :: List.replicate padding none
      else publicBits.map some ++ none :: List.replicate padding none
    let input : Tape := { left := before, right := tail }
    ∃ finish used after remaining,
      RunsFor GuardedCompiler.seekScratchInput
        ({ inputTape := input.moveRight.moveRight, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape.moveLeft = { left := after, right := List.replicate remaining none } := by
  let bits := if gap then publicBits else publicBits.tail
  let rest : List (Option Bool) :=
    List.replicate (if gap || !publicBits.isEmpty then padding else padding - 1) none
  let saved := if gap then none :: none :: before
    else (publicBits.head?.map some).getD none :: none :: before
  let source : Tape :=
    { left := before, right := if gap then none :: publicBits.map some ++ none :: List.replicate padding none
        else publicBits.map some ++ none :: List.replicate padding none }
  have hEntry :
      ({ inputTape := source.moveRight.moveRight, outputTape := output } : Configuration) =
        seekBitstringNextStart saved bits rest output := by
    rw [seekBitstringNextStart_layout]
    cases gap <;> cases publicBits with
    | nil => cases padding <;> simp [source, bits, rest, saved, Tape.moveRight, List.replicate_succ]
    | cons bit remaining =>
        cases remaining <;> cases padding <;>
          simp [source, bits, rest, saved, Tape.moveRight, List.replicate_succ]
  refine ⟨seekBitstringNextFinish saved bits rest output, 3 * bits.length + 3,
    bits.reverse.map some ++ saved, max 1 rest.length, ?_, rfl, rfl, ?_⟩
  · rw [hEntry]
    exact seekBitstringNext_runs saved bits rest output
  · rw [seekBitstringNextFinish_layout_cells]
    dsimp only [rest]
    cases hPad : (if gap || !publicBits.isEmpty then padding else padding - 1) <;>
      simp [Tape.moveRight, Tape.moveLeft, List.replicate_succ]

/-- Every native rewind/scan/copy in saved-message framing stops on finite
tapes, even when delimiters are malformed or the scratch cells are dirty.
This theorem concerns actual stopping overhead, not successful serialization
or preservation of an invalid protocol layout. No caller tape is reset. -/
private theorem frameSavedMessage_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∀ savedInput inputBlanks savedOutput outputBlanks,
        input = ({ left := none :: savedInput, right := List.replicate inputBlanks none } : Tape) →
        output = ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape) →
        ∃ (payload : List Bool), ∃ remainingInput afterOutput remainingOutput,
          finish.inputTape = {
            left := payload.reverse.map some ++ none :: savedInput
            right := List.replicate remainingInput none } ∧
          finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none }) := by
  obtain ⟨first, t₁, h₁, run₁, halt₁, output₁⟩ := rewindBitstring_terminates_from output input
  let firstPhysical := first.swapTapes
  let secondStart : Configuration :=
    { pc := 7, inputTape := firstPhysical.inputTape, outputTape := firstPhysical.outputTape.moveLeft.moveLeft }
  obtain ⟨second, t₂, h₂, run₂, halt₂, output₂⟩ :=
    rewindBitstring_terminates_from secondStart.outputTape secondStart.inputTape
  let secondPhysical := second.swapTapes
  obtain ⟨copied, t₃, h₃, run₃, halt₃⟩ :=
    copyBitstring_terminates_from_anyTape secondPhysical.outputTape secondPhysical.inputTape
  let copiedPhysical := copied.swapTapes
  let seekStart : Configuration :=
    { pc := 23, inputTape := copiedPhysical.inputTape, outputTape := copiedPhysical.outputTape.moveRight.moveRight }
  obtain ⟨sought, t₄, h₄, run₄, halt₄, output₄⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape seekStart.outputTape seekStart.inputTape
  let soughtPhysical := sought.swapTapes
  let rewindStart : Configuration :=
    { pc := 30, inputTape := soughtPhysical.inputTape, outputTape := soughtPhysical.outputTape.moveLeft }
  obtain ⟨rewound, t₅, h₅, run₅, halt₅, _output₅⟩ :=
    rewindBitstring_terminates_from rewindStart.inputTape rewindStart.outputTape
  obtain ⟨framed, t₆, h₆, run₆, halt₆⟩ :=
    writeFrame_terminates_from_anyTape rewound.inputTape rewound.outputTape
  let a := rewindBitstring.swapTapes.asSubroutine 0 5
  let b := rewindBitstring.swapTapes.asSubroutine 7 12
  let k := copyBitstring.swapTapes.asSubroutine 12 21
  let s := GuardedCompiler.seekScratchInput.swapTapes.asSubroutine 23 29
  let r := rewindBitstring.asSubroutine 30 35
  let f := writeFrame.asSubroutine 35 60
  have firstRun := run₁.swapTapes.withSubroutine_halted_of_closed
    [] rewindBitstring.swapTapes
    ([.moveLeft .output, .moveLeft .output] ++ b ++ k ++ [.moveRight .output, .moveRight .output] ++
      s ++ [.moveLeft .output] ++ r ++ f ++ [.halt]) 5
    (by change 0 < 4; decide) rfl halt₁ (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  change RunsFor frameSavedMessage
    ({ inputTape := input, outputTape := output } : Configuration) (firstPhysical.resumeAt 5) t₁ at firstRun
  let firstBack : Configuration :=
    { pc := 6, inputTape := firstPhysical.inputTape, outputTape := firstPhysical.outputTape.moveLeft }
  have back₁ : Step frameSavedMessage (firstPhysical.resumeAt 5) firstBack := by
    have code : frameSavedMessage[5]? = some (.moveLeft .output) := rfl
    simp [Step, successors, next, Configuration.resumeAt, code, firstBack,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have back₂ : Step frameSavedMessage firstBack secondStart := by
    have code : frameSavedMessage[6]? = some (.moveLeft .output) := rfl
    simp [Step, successors, next, code, firstBack, secondStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toSecond := RunsFor.succ (RunsFor.succ firstRun back₁) back₂
  have secondRun := run₂.swapTapes.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .output, .moveLeft .output]) rewindBitstring.swapTapes
    (k ++ [.moveRight .output, .moveRight .output] ++ s ++ [.moveLeft .output] ++ r ++ f ++ [.halt]) 12
    (by change 0 < 4; decide) rfl halt₂ (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  change RunsFor frameSavedMessage secondStart (secondPhysical.resumeAt 12) t₂ at secondRun
  have toCopy := toSecond.trans secondRun
  have copyRun := run₃.swapTapes.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .output, .moveLeft .output] ++ b) copyBitstring.swapTapes
    ([.moveRight .output, .moveRight .output] ++ s ++ [.moveLeft .output] ++ r ++ f ++ [.halt]) 21
    (by change 0 < 8; decide) rfl halt₃ (Program.controlClosed_swapTapes _ GuardedCompiler.copyBitstring_control_closed)
  change RunsFor frameSavedMessage (secondPhysical.resumeAt 12) (copiedPhysical.resumeAt 21) t₃ at copyRun
  let firstForward : Configuration :=
    { pc := 22, inputTape := copiedPhysical.inputTape, outputTape := copiedPhysical.outputTape.moveRight }
  have forward₁ : Step frameSavedMessage (copiedPhysical.resumeAt 21) firstForward := by
    have code : frameSavedMessage[21]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, Configuration.resumeAt, code, firstForward,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have forward₂ : Step frameSavedMessage firstForward seekStart := by
    have code : frameSavedMessage[22]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, firstForward, seekStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toSeek := RunsFor.succ (RunsFor.succ (toCopy.trans copyRun) forward₁) forward₂
  have seekRun := run₄.swapTapes.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .output, .moveLeft .output] ++ b ++ k ++ [.moveRight .output, .moveRight .output])
    GuardedCompiler.seekScratchInput.swapTapes ([.moveLeft .output] ++ r ++ f ++ [.halt]) 29
    (by change 0 < 5; decide) rfl halt₄ (Program.controlClosed_swapTapes _ GuardedCompiler.seekScratchInput_control_closed)
  change RunsFor frameSavedMessage seekStart (soughtPhysical.resumeAt 29) t₄ at seekRun
  have back₃ : Step frameSavedMessage (soughtPhysical.resumeAt 29) rewindStart := by
    have code : frameSavedMessage[29]? = some (.moveLeft .output) := rfl
    simp [Step, successors, next, Configuration.resumeAt, code, rewindStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toRewind := RunsFor.succ (toSeek.trans seekRun) back₃
  have rewindRun := run₅.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .output, .moveLeft .output] ++ b ++ k ++ [.moveRight .output, .moveRight .output] ++
      s ++ [.moveLeft .output]) rewindBitstring (f ++ [.halt]) 35
    (by change 0 < 4; decide) rfl halt₅ rewindBitstring_control_closed
  change RunsFor frameSavedMessage rewindStart (rewound.resumeAt 35) t₅ at rewindRun
  have toFrame := toRewind.trans rewindRun
  have frameRun := run₆.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .output, .moveLeft .output] ++ b ++ k ++ [.moveRight .output, .moveRight .output] ++
      s ++ [.moveLeft .output] ++ r) writeFrame [.halt] 60
    (by change 0 < 24; decide) rfl halt₆ writeFrame_control_closed
  change RunsFor frameSavedMessage (rewound.resumeAt 35) (framed.resumeAt 60) t₆ at frameRun
  let finish : Configuration := { framed with pc := 60, halted := true }
  have last : Step frameSavedMessage (framed.resumeAt 60) finish := by
    have code : frameSavedMessage[60]? = some .halt := rfl
    simp [Step, successors, next, Configuration.resumeAt, code, finish, Instruction.next]
  refine ⟨finish, ((t₁ + 1 + 1 + t₂ + t₃ + 1 + 1 + t₄ + 1) + t₅) + t₆ + 1, ?_,
    RunsFor.succ (toFrame.trans frameRun) last, rfl, ?_⟩
  · have storage₂ := GuardedCompiler.sourceStorage_le_of_run toSecond
    have storage₃ := GuardedCompiler.sourceStorage_le_of_run toCopy
    have storage₄ := GuardedCompiler.sourceStorage_le_of_run toSeek
    have storage₅ := GuardedCompiler.sourceStorage_le_of_run toRewind
    have storage₆ := GuardedCompiler.sourceStorage_le_of_run toFrame
    have left₁ : output.left.length ≤ output.cells := by dsimp only [Tape.cells]; omega
    have left₂ : secondStart.outputTape.left.length ≤ secondStart.outputTape.cells := by dsimp only [Tape.cells]; omega
    have left₅ : rewindStart.inputTape.left.length ≤ rewindStart.inputTape.cells := by dsimp only [Tape.cells]; omega
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at storage₂ storage₃ storage₄ storage₅ storage₆
    change t₃ ≤ 6 * secondPhysical.outputTape.cells + 2 at h₃
    change t₆ ≤ 200 * (rewound.inputTape.cells + rewound.outputTape.cells) + 200 at h₆
    omega
  · intro savedInput inputBlanks savedOutput outputBlanks hInput hOutput
    obtain ⟨firstExact, publicBits, firstBefore, _hPublicLength, firstExactRun,
      firstExactHalt, firstExactInput, _firstExactOutput⟩ :=
      rewindBitstring_terminates_with_layout output input
    have hFirst := run₁.halted_finish_eq_of_no_randomBit firstExactRun
      halt₁ firstExactHalt rewindBitstring_no_randomBit
    have hFirstInput : first.inputTape =
        { ({ right := publicBits.map some ++ none :: List.replicate outputBlanks none } : Tape).moveRight
          with left := none :: firstBefore } := by
      rw [hFirst, firstExactInput, hOutput]
      rfl
    have hSecondRight : secondStart.outputTape.right =
        none :: publicBits.map some ++ none :: List.replicate outputBlanks none := by
      change first.inputTape.moveLeft.moveLeft.right = _
      rw [hFirstInput]
      cases publicBits <;> cases firstBefore <;> simp [Tape.moveRight, Tape.moveLeft]
    obtain ⟨secondExact, leading, secondBefore, _hLeadingLength, secondExactRun,
      secondExactHalt, secondExactInput, _secondExactOutput⟩ :=
      rewindBitstring_terminates_with_layout secondStart.outputTape secondStart.inputTape
    have hSecond := run₂.halted_finish_eq_of_no_randomBit secondExactRun
      halt₂ secondExactHalt rewindBitstring_no_randomBit
    have hSecondInput : second.inputTape =
        { ({ right := leading.map some ++ secondStart.outputTape.current :: secondStart.outputTape.right } : Tape).moveRight
          with left := none :: secondBefore } := by
      rw [hSecond, secondExactInput]
      rfl
    have hSecondOther : second.outputTape = input := by
      rw [output₂]
      exact output₁
    have hCopied : ∃ (payload : List Bool) (gap : Bool),
        copied.inputTape =
          { left := payload.reverse.map some ++ none :: secondBefore,
            right := if gap then none :: publicBits.map some ++ none :: List.replicate outputBlanks none
              else publicBits.map some ++ none :: List.replicate outputBlanks none } ∧
        copied.outputTape =
          { left := payload.reverse.map some ++ none :: savedInput,
            right := List.replicate (inputBlanks - payload.length) none } := by
      cases hCurrent : secondStart.outputTape.current with
      | none =>
          let tail := none :: publicBits.map some ++ none :: List.replicate outputBlanks none
          have hEntry :
              ({ inputTape := secondPhysical.outputTape, outputTape := secondPhysical.inputTape } : Configuration) =
                copySegmentStart (none :: secondBefore) (none :: savedInput) tail leading inputBlanks := by
            simp only [copySegmentStart_layout, secondPhysical, Configuration.swapTapes,
              hSecondInput, hSecondOther, hInput, hCurrent, hSecondRight, tail]
          have segmentRun := copySegment_runs (none :: secondBefore) (none :: savedInput) tail leading inputBlanks
          rw [← hEntry] at segmentRun
          have hCopy := run₃.halted_finish_eq_of_no_randomBit segmentRun
            halt₃ rfl copyBitstring_no_randomBit
          exact ⟨leading, true, by rw [hCopy]; rfl, by rw [hCopy]; rfl⟩
      | some bit =>
          let payload := leading ++ [bit]
          let tail := publicBits.map some ++ none :: List.replicate outputBlanks none
          have hEntry :
              ({ inputTape := secondPhysical.outputTape, outputTape := secondPhysical.inputTape } : Configuration) =
                copySegmentStart (none :: secondBefore) (none :: savedInput) tail payload inputBlanks := by
            simp only [copySegmentStart_layout, secondPhysical, Configuration.swapTapes,
              hSecondInput, hSecondOther, hInput, hCurrent, hSecondRight, payload, tail,
              List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.cons_append, List.nil_append]
          have segmentRun := copySegment_runs (none :: secondBefore) (none :: savedInput) tail payload inputBlanks
          rw [← hEntry] at segmentRun
          have hCopy := run₃.halted_finish_eq_of_no_randomBit segmentRun
            halt₃ rfl copyBitstring_no_randomBit
          exact ⟨payload, false, by rw [hCopy]; rfl, by rw [hCopy]; rfl⟩
    obtain ⟨payload, gap, hCopyInput, hCopyOutput⟩ := hCopied
    obtain ⟨frontier, frontierTime, afterOutput, outputRemaining, frontierRun,
      frontierHalt, _frontierOther, frontierOutput⟩ :=
      savedMessage_seek_frontier (payload.reverse.map some ++ none :: secondBefore)
        publicBits outputBlanks gap copied.outputTape
    have frontierRun' : RunsFor GuardedCompiler.seekScratchInput
        ({ inputTape := seekStart.outputTape, outputTape := seekStart.inputTape } : Configuration)
        frontier frontierTime := by
      change RunsFor GuardedCompiler.seekScratchInput
        ({ inputTape := copied.inputTape.moveRight.moveRight, outputTape := copied.outputTape } : Configuration)
        frontier frontierTime
      rw [hCopyInput]
      exact frontierRun
    have hFrontier := run₄.halted_finish_eq_of_no_randomBit frontierRun'
      halt₄ frontierHalt GuardedCompiler.seekScratchInput_no_randomBit
    have hRestoredOutput : rewindStart.outputTape =
        { left := afterOutput, right := List.replicate outputRemaining none } := by
      change sought.inputTape.moveLeft = _
      rw [hFrontier]
      exact frontierOutput
    have hScratch : rewindStart.inputTape =
        { left := payload.reverse.map some ++ none :: savedInput,
          right := List.replicate (inputBlanks - payload.length) none } := by
      change sought.outputTape = _
      rw [output₄]
      exact hCopyOutput
    have scratchRun := rewindScratch_runs_from savedInput payload none
      (List.replicate (inputBlanks - payload.length) none) rewindStart.outputTape
    have hScratchEntry :
        ({ inputTape := rewindStart.inputTape, outputTape := rewindStart.outputTape } : Configuration) =
          { inputTape := { left := payload.reverse.map some ++ none :: savedInput, right := List.replicate (inputBlanks - payload.length) none },
            outputTape := rewindStart.outputTape } := by rw [hScratch]
    rw [← hScratchEntry] at scratchRun
    have hRewind := run₅.halted_finish_eq_of_no_randomBit scratchRun
      halt₅ rfl rewindBitstring_no_randomBit
    have hFrameEntry :
        ({ inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration) =
          writeFrameContextPaddedStart savedInput afterOutput
            (List.replicate (inputBlanks - payload.length) none) payload outputRemaining := by
      rw [hRewind, writeFrameContextPaddedStart_layout, hRestoredOutput]
      cases payload <;> simp [Tape.moveRight]
    have exactFrameRun := writeFrameContextPadded_runs savedInput afterOutput
      (List.replicate (inputBlanks - payload.length) none) payload outputRemaining
    rw [← hFrameEntry] at exactFrameRun
    have hFrame := run₆.halted_finish_eq_of_no_randomBit exactFrameRun
      halt₆ rfl writeFrame_no_randomBit
    refine ⟨payload, inputBlanks - payload.length,
      (frame payload).reverse.map some ++ afterOutput,
      outputRemaining - (2 * payload.length + 1), ?_, ?_⟩
    · change framed.inputTape = _
      rw [hFrame]
      rfl
    · change framed.outputTape = _
      rw [hFrame]
      rfl

theorem frameSavedMessage_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := frameSavedMessage_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Saved-message framing preserves fresh frontiers on both physical tapes
when input scratch has a reserved separator. The saved output cells may be
arbitrary, and the recovered payload may be empty or malformed. Its actual
rewind/copy/scan transitions determine the copied block and restored head;
no valid DDH fields, canonical normalizer reply, or caller reset is assumed. -/
theorem frameSavedMessage_terminates_with_fresh_tapes
    (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000 *
        (({ left := none :: savedInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := { left := none :: savedInput, right := List.replicate inputBlanks none },
           outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    frameSavedMessage_terminates_core
      { left := none :: savedInput, right := List.replicate inputBlanks none }
      { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨payload, remainingInput, afterOutput, remainingOutput, hInput, hOutput⟩ :=
    hLayout savedInput inputBlanks savedOutput outputBlanks rfl rfl
  exact ⟨finish, used, payload.reverse.map some ++ none :: savedInput,
    remainingInput, afterOutput, remainingOutput, hBound, run, hHalted, hInput, hOutput⟩

/-- Saved-message framing appends precisely one actual contiguous raw block
before the protected input separator. Earlier stored cells remain unchanged,
including malformed replies. Both heads finish at fresh blank frontiers;
this is a physical tape postcondition of the native copy and frame trace. -/
theorem frameSavedMessage_terminates_with_retained_input
    (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    ∃ finish used, ∃ (payload : List Bool), ∃ remainingInput afterOutput remainingOutput,
      used ≤ 1000000 *
        (({ left := none :: savedInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := { left := none :: savedInput, right := List.replicate inputBlanks none },
           outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = {
        left := payload.reverse.map some ++ none :: savedInput
        right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    frameSavedMessage_terminates_core
      { left := none :: savedInput, right := List.replicate inputBlanks none }
      { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨payload, remainingInput, afterOutput, remainingOutput, hInput, hOutput⟩ :=
    hLayout savedInput inputBlanks savedOutput outputBlanks rfl rfl
  exact ⟨finish, used, payload, remainingInput, afterOutput, remainingOutput,
    hBound, run, hHalted, hInput, hOutput⟩

end Machine
