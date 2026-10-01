import Foundation.Machine.MultiplyPrefixPreparation
import Foundation.Machine.StoredInputScratch
import Foundation.Machine.SavedMessageFraming

namespace Machine

/-- After the public multiplication prefix has been copied, reach fresh
scratch without changing stored DDH/choose data, then append the selected
message frame. Both routines execute their native instructions on the actual
caller tapes; the selected raw code and challenge remain protected. -/
def prepareMultiplyMessage : Program :=
  seekStoredInputScratch.asSubroutine 0 20 ++ frameSavedMessage.asSubroutine 20 82 ++ [.halt]

def prepareMultiplyMessageStart (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) (blanks : Nat) : Configuration :=
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  seekStoredInputScratchStart (publicBits.reverse.map some ++ none :: beforeInput)
    (true :: tupleTail) reply canonical blanks
    { left := publicBits.reverse.map some ++ none :: none :: selected.reverse.map some ++ none :: savedOutput }

def prepareMultiplyMessageFinish (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) (blanks : Nat) : Configuration :=
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
  { frameSavedMessageFinish
      (canonical.reverse.map some ++ none :: reply.reverse.map some ++ none ::
        original.reverse.map some ++ none :: beforeInput)
      savedOutput (encodeSecurityParameter n ++ frame instanceBits) selected (blanks - 1) with pc := 82 }

def prepareMultiplyMessageSteps (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) : Nat :=
  seekStoredInputScratchSteps (true :: tupleTail) reply canonical +
    frameSavedMessageSteps (encodeSecurityParameter n ++ frame instanceBits) selected + 1

theorem prepareMultiplyMessage_runs (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) (blanks : Nat) :
    RunsFor prepareMultiplyMessage
      (prepareMultiplyMessageStart beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks)
      (prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks)
      (prepareMultiplyMessageSteps n instanceBits tupleTail reply canonical selected) := by
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let original := publicBits ++ true :: tupleTail
  let output : Tape :=
    { left := publicBits.reverse.map some ++ none :: none :: selected.reverse.map some ++ none :: savedOutput }
  let before := publicBits.reverse.map some ++ none :: beforeInput
  let saved := canonical.reverse.map some ++ none :: reply.reverse.map some ++ none ::
    original.reverse.map some ++ none :: beforeInput
  have hSeek := (seekStoredInputScratch_runs before (true :: tupleTail) reply canonical blanks output).withSubroutine_halted_of_closed
    [] seekStoredInputScratch (frameSavedMessage.asSubroutine 20 82 ++ [.halt]) 20
    (by change 0 < 19; decide) rfl rfl seekStoredInputScratch_control_closed
  change RunsFor prepareMultiplyMessage
    (prepareMultiplyMessageStart beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks)
    ((seekStoredInputScratchFinish before (true :: tupleTail) reply canonical blanks output).resumeAt 20)
    (seekStoredInputScratchSteps (true :: tupleTail) reply canonical) at hSeek
  have hFrameStart : (seekStoredInputScratchFinish before (true :: tupleTail) reply canonical blanks output).resumeAt 20 =
      (frameSavedMessageStart saved savedOutput publicBits selected (blanks - 1)).rebasePc 20 := by
    simp [seekStoredInputScratchFinish, frameSavedMessageStart, before, saved, original,
      Configuration.resumeAt, Configuration.rebasePc, output, List.reverse_append,
      List.map_append, List.append_assoc]
  rw [hFrameStart] at hSeek
  have hFrame := (frameSavedMessage_runs saved savedOutput publicBits selected (blanks - 1)).withSubroutine_halted_of_closed
    (seekStoredInputScratch.asSubroutine 0 20) frameSavedMessage [.halt] 82
    (by change 0 < 61; decide) rfl rfl frameSavedMessage_control_closed
  change RunsFor prepareMultiplyMessage
    ((frameSavedMessageStart saved savedOutput publicBits selected (blanks - 1)).rebasePc 20)
    ((prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks).resumeAt 82)
    (frameSavedMessageSteps publicBits selected) at hFrame
  have hHalt : Step prepareMultiplyMessage
      ((prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks).resumeAt 82)
      (prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks) := by
    simp [Step, successors, next, prepareMultiplyMessage, seekStoredInputScratch, frameSavedMessage,
      GuardedCompiler.seekScratchInput, rewindBitstring, copyBitstring, writeFrame, writeFrameHeader,
      Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, prepareMultiplyMessageFinish, frameSavedMessageFinish, Instruction.next]
  exact RunsFor.succ (hSeek.trans hFrame) hHalt

theorem prepareMultiplyMessage_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareMultiplyMessage := by
  simp [prepareMultiplyMessage, seekStoredInputScratch, frameSavedMessage,
    GuardedCompiler.seekScratchInput, rewindBitstring, copyBitstring, writeFrame, writeFrameHeader,
    Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareMultiplyMessage_eval (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) (blanks : Nat) :
    evalConfigWithin prepareMultiplyMessage
      (prepareMultiplyMessageStart beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks)
      (prepareMultiplyMessageSteps n instanceBits tupleTail reply canonical selected) =
      PMF.pure (prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks) :=
  (prepareMultiplyMessage_runs beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks).evalConfigWithin_eq_pure_of_no_randomBit
    prepareMultiplyMessage_no_randomBit

/-- The operand is appended contiguously to the exact certified arithmetic
public input, in selected-message-first order. Earlier saved cells are still
separated from this new request by real blank cells. -/
theorem prepareMultiplyMessageFinish_output (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected : List Bool) (blanks : Nat) :
    (prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame selected).reverse.map some ++
          none :: none :: selected.reverse.map some ++ none :: savedOutput } := by
  simp [prepareMultiplyMessageFinish, frameSavedMessageFinish, List.append_assoc]

theorem prepareMultiplyMessage_steps_le (n : Nat)
    (instanceBits tupleTail reply canonical selected : List Bool) :
    prepareMultiplyMessageSteps n instanceBits tupleTail reply canonical selected ≤
      5 * (encodeSecurityParameter n ++ frame instanceBits).length +
        3 * (tupleTail.length + reply.length + canonical.length) + 23 * selected.length + 48 := by
  have h := frameSavedMessage_steps_le (encodeSecurityParameter n ++ frame instanceBits) selected
  rw [prepareMultiplyMessageSteps, seekStoredInputScratch_steps_eq]
  simp only [List.length_cons]
  omega

/-- Connect a real returned prefix configuration with a split canonical
response. The equality joins existing tape cells only; it is not a new
machine input load, decode, or copy operation. -/
theorem prepareMultiplyPrefixFinish_message_layout (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed remaining selected : List Bool) (blanks : Nat)
    (current : Option Bool) (right : List (Option Bool))
    (hTail : current :: right = remaining.map some ++ none :: List.replicate blanks none) :
    (prepareMultiplyPrefixFinish beforeInput (none :: savedOutput) n instanceBits tupleTail reply consumed selected current right).resumeAt 0 =
      prepareMultiplyMessageStart beforeInput savedOutput n instanceBits tupleTail reply (consumed ++ remaining) selected blanks := by
  simp only [prepareMultiplyPrefixFinish, preparePublicPrefixContextFinish_layout,
    Configuration.resumeAt, prepareMultiplyMessageStart, seekStoredInputScratchStart,
    seekBitstringNextStart_layout]
  simp [Tape.moveRight, List.map_append, List.append_assoc, hTail]

/-- The complete scratch scan and saved-message framing stage stops on
arbitrary finite caller tapes. Its time is bounded in the actual retained
storage, independently of canonical response or public-input validity. -/
theorem prepareMultiplyMessage_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 200000000 * (input.cells + output.cells) + 200000000 ∧
      RunsFor prepareMultiplyMessage
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨sought, seekTime, hSeekTime, seekRun, seekHalt, _seekOutput⟩ :=
    seekStoredInputScratch_terminates_from_anyTape input output
  obtain ⟨framed, frameTime, hFrameTime, frameRun, frameHalt⟩ :=
    frameSavedMessage_terminates_from_anyTape sought.inputTape sought.outputTape
  have hSeek := seekRun.withSubroutine_halted_of_closed
    [] seekStoredInputScratch (frameSavedMessage.asSubroutine 20 82 ++ [.halt]) 20
    (by change 0 < 19; decide) rfl seekHalt seekStoredInputScratch_control_closed
  change RunsFor prepareMultiplyMessage
    ({ inputTape := input, outputTape := output } : Configuration) (sought.resumeAt 20) seekTime at hSeek
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (seekStoredInputScratch.asSubroutine 0 20) frameSavedMessage [.halt] 82
    (by change 0 < 61; decide) rfl frameHalt frameSavedMessage_control_closed
  change RunsFor prepareMultiplyMessage (sought.resumeAt 20) (framed.resumeAt 82) frameTime at hFrame
  let finish : Configuration := { framed with pc := 82, halted := true }
  have last : Step prepareMultiplyMessage (framed.resumeAt 82) finish := by
    have code : prepareMultiplyMessage[82]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, seekTime + frameTime + 1, ?_, RunsFor.succ (hSeek.trans hFrame) last, rfl⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run seekRun
  change sought.inputTape.cells + sought.outputTape.cells ≤ input.cells + output.cells + seekTime at hStorage
  omega

end Machine
