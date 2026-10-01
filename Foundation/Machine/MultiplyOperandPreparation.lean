import Foundation.Machine.MultiplyMessagePreparation
import Foundation.Machine.ScratchInputRestoration
import Foundation.Machine.StoredElementFraming

namespace Machine

/-- Complete the represented multiplication request from the actual stored
message scratch and DDH input. Restore the original input by native rewinds,
then append its final element frame after the selected message operand. -/
def prepareMultiplyOperands : Program :=
  restoreInputBeforeScratch.asSubroutine 0 27 ++ frameStoredFinalElement.asSubroutine 27 112 ++ [.halt]

private def multiplicationPrefix (n : Nat) (instanceBits selected : List Bool) : List Bool :=
  encodeSecurityParameter n ++ frame instanceBits ++ frame selected

private def multiplicationSavedOutput (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits selected : List Bool) : List (Option Bool) :=
  (multiplicationPrefix n instanceBits selected).reverse.map some ++
    none :: none :: selected.reverse.map some ++ none :: savedOutput

private def ddhStoredBits (n : Nat) (instanceBits first second last : List Bool) : List Bool :=
  encodeSecurityParameter n ++ frame instanceBits ++
    frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)

private def arithmeticStoredTail (reply canonical selected : List Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  reply.map some ++ none :: canonical.map some ++ none :: selected.map some ++ none :: padding

def prepareMultiplyOperandsStart (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) : Configuration :=
  restoreInputBeforeScratchStart beforeInput (ddhStoredBits n instanceBits first second last)
    reply canonical selected padding
    { left := multiplicationSavedOutput savedOutput n instanceBits selected }

def prepareMultiplyOperandsFinish (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) : Configuration :=
  { frameStoredFinalElementFinish beforeInput (multiplicationSavedOutput savedOutput n instanceBits selected)
      (arithmeticStoredTail reply canonical selected padding) n instanceBits first second last with pc := 112 }

def prepareMultiplyOperandsSteps (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) : Nat :=
  restoreInputBeforeScratchSteps (ddhStoredBits n instanceBits first second last) reply canonical selected +
    frameStoredFinalElementSteps n instanceBits first second last + 1

/-- The native restoration and final-element framing have linear overhead
in the retained input and response lengths, including the selected scratch. -/
theorem prepareMultiplyOperands_steps_le (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) :
    prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected ≤
      5*n + 14*instanceBits.length + 18*(first.length + second.length) +
        22*last.length + 2*(reply.length + canonical.length + selected.length) + 83 := by
  have hRestore := restoreInputBeforeScratch_steps_eq
    (ddhStoredBits n instanceBits first second last) reply canonical selected
  have hFrame := frameStoredFinalElement_steps_le n instanceBits first second last
  simp only [prepareMultiplyOperandsSteps, hRestore]
  simp [ddhStoredBits, frame, encodeSecurityParameter,
    FiniteBitEncoding.delimit_length] at *
  omega

theorem prepareMultiplyOperands_runs (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) :
    RunsFor prepareMultiplyOperands
      (prepareMultiplyOperandsStart beforeInput savedOutput padding n instanceBits first second last reply canonical selected)
      (prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected)
      (prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected) := by
  let original := ddhStoredBits n instanceBits first second last
  let output : Tape := { left := multiplicationSavedOutput savedOutput n instanceBits selected }
  let tail := arithmeticStoredTail reply canonical selected padding
  have hRestore := (restoreInputBeforeScratch_runs beforeInput original reply canonical selected padding output).withSubroutine_halted_of_closed
    [] restoreInputBeforeScratch (frameStoredFinalElement.asSubroutine 27 112 ++ [.halt]) 27
    (by change 0 < 26; decide) rfl rfl restoreInputBeforeScratch_control_closed
  change RunsFor prepareMultiplyOperands
    (prepareMultiplyOperandsStart beforeInput savedOutput padding n instanceBits first second last reply canonical selected)
    ((restoreInputBeforeScratchFinish beforeInput original reply canonical selected padding output).resumeAt 27)
    (restoreInputBeforeScratchSteps original reply canonical selected) at hRestore
  let elementStart := frameStoredFinalElementStart beforeInput output.left tail n instanceBits first second last
  have hElementStart : (restoreInputBeforeScratchFinish beforeInput original reply canonical selected padding output).resumeAt 27 =
      elementStart.rebasePc 27 := by
    cases n <;> simp [restoreInputBeforeScratchFinish, restoreStoredInputFinish,
      elementStart, frameStoredFinalElementStart_layout, original, ddhStoredBits,
      tail, arithmeticStoredTail, output, Configuration.resumeAt, Configuration.rebasePc,
      encodeSecurityParameter, List.map_append, List.map_replicate, List.append_assoc,
      List.replicate_succ, Tape.moveRight]
  rw [hElementStart] at hRestore
  have hElement := (frameStoredFinalElement_runs beforeInput output.left tail n instanceBits first second last).withSubroutine_halted_of_closed
    (restoreInputBeforeScratch.asSubroutine 0 27) frameStoredFinalElement [.halt] 112
    (by change 0 < 84; decide) rfl rfl frameStoredFinalElement_control_closed
  change RunsFor prepareMultiplyOperands (elementStart.rebasePc 27)
    ((prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected).resumeAt 112)
    (frameStoredFinalElementSteps n instanceBits first second last) at hElement
  have hHalt : Step prepareMultiplyOperands
      ((prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected).resumeAt 112)
      (prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected) := by
    have hCode : prepareMultiplyOperands[112]? = some .halt := by
      simp [prepareMultiplyOperands, restoreInputBeforeScratch, restoreStoredInput, rewindBitstring,
        frameStoredFinalElement, skipUnary, skipFrame, skipDelimited, writeFrameAfterFalse,
        writeFrame, writeFrameHeader, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]
    simp [Step, successors, next, prepareMultiplyOperandsFinish,
      frameStoredFinalElementFinish, writeFrameAfterFalseFinish, Configuration.resumeAt, hCode, Instruction.next]
  exact RunsFor.succ (hRestore.trans hElement) hHalt

theorem prepareMultiplyOperands_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareMultiplyOperands := by
  simp [prepareMultiplyOperands, restoreInputBeforeScratch, restoreStoredInput, rewindBitstring,
    frameStoredFinalElement, skipUnary, skipFrame, skipDelimited, writeFrameAfterFalse,
    writeFrame, writeFrameHeader, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareMultiplyOperands_eval (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) :
    evalConfigWithin prepareMultiplyOperands
      (prepareMultiplyOperandsStart beforeInput savedOutput padding n instanceBits first second last reply canonical selected)
      (prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected) =
      PMF.pure (prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected) :=
  (prepareMultiplyOperands_runs beforeInput savedOutput padding n instanceBits first second last reply canonical selected).evalConfigWithin_eq_pure_of_no_randomBit
    prepareMultiplyOperands_no_randomBit

/-- Exact completed request layout. Its selected-message-first operand
order is the one used by the ElGamal challenge ciphertext specification. -/
theorem prepareMultiplyOperandsFinish_output (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) :
    (prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).reverse.map some ++
          none :: none :: selected.reverse.map some ++ none :: savedOutput,
        right := List.replicate (instanceBits.length + 1 - (2 * last.length + 1)) none } := by
  simp only [prepareMultiplyOperandsFinish]
  rw [frameStoredFinalElementFinish_output]
  simp [multiplicationSavedOutput, multiplicationPrefix, List.reverse_append, List.map_append, List.append_assoc]

theorem prepareMultiplyOperandsFinish_input (beforeInput savedOutput padding : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) :
    (prepareMultiplyOperandsFinish beforeInput savedOutput padding n instanceBits first second last reply canonical selected).inputTape =
      { ({ right := last.map some ++ none :: reply.map some ++ none :: canonical.map some ++
            none :: selected.map some ++ none :: padding } : Tape).moveRight with
        left := (FiniteBitEncoding.delimit second).reverse.map some ++
          (FiniteBitEncoding.delimit first).reverse.map some ++
          (encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length).reverse.map some ++
          (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput } := by
  simp only [prepareMultiplyOperandsFinish]
  rw [frameStoredFinalElementFinish_input]
  simp only [arithmeticStoredTail, List.append_assoc, List.cons_append]

/-- The preceding message-framing stage returns this actual caller state,
including stored original, reply, canonical response, scratch, and padding. -/
theorem prepareMultiplyMessageFinish_operands_layout (beforeInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    let tuple := FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last
    let tupleTail := (List.replicate (tuple.length - 1) true ++ false :: tuple)
    (prepareMultiplyMessageFinish beforeInput savedOutput n instanceBits tupleTail reply canonical selected blanks).resumeAt 0 =
      prepareMultiplyOperandsStart beforeInput savedOutput (List.replicate ((blanks - 1) - selected.length) none)
        n instanceBits first second last reply canonical selected := by
  dsimp only
  have hPositive : 0 < (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length := by
    simp only [List.length_append, FiniteBitEncoding.delimit_length]
    omega
  have hFrame : true :: (List.replicate
      ((FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length - 1) true ++
      false :: (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)) =
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) := by
    have hLen : (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length - 1 + 1 =
        (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length := by omega
    have hRep : List.replicate (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length true =
        true :: List.replicate ((FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length - 1) true := by
      calc
        _ = List.replicate ((FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length - 1 + 1) true :=
          congrArg (fun m => List.replicate m true) hLen.symm
        _ = _ := List.replicate_succ
    simp only [frame]
    rw [hRep]
    simp
  simp only [prepareMultiplyMessageFinish, frameSavedMessageFinish, prepareMultiplyOperandsStart,
    restoreInputBeforeScratchStart, ddhStoredBits, multiplicationSavedOutput, multiplicationPrefix,
    Configuration.resumeAt]
  rw [hFrame]
  simp [List.append_assoc]


/-- Restoration and final-element framing terminate on arbitrary retained
caller tapes. The resource bound follows the actual configurations between
subroutines, without assuming a valid stored DDH tuple or normalized reply. -/
private theorem prepareMultiplyOperands_terminates_layout_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000 * (input.cells + output.cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∀ beforeOutput blanks,
        output = ({ left := beforeOutput, right := List.replicate blanks none } : Tape) →
        ∃ saved remaining,
          finish.outputTape = { left := saved, right := List.replicate remaining none }) := by
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreInputBeforeScratch_terminates_from_anyTape input output
  obtain ⟨framed, frameTime, hFrameTime, frameRun, frameHalt⟩ :=
    frameStoredFinalElement_terminates_from_anyTape restored.inputTape restored.outputTape
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreInputBeforeScratch (frameStoredFinalElement.asSubroutine 27 112 ++ [.halt]) 27
    (by change 0 < 26; decide) rfl restoreHalt restoreInputBeforeScratch_control_closed
  change RunsFor prepareMultiplyOperands
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 27) restoreTime at hRestore
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (restoreInputBeforeScratch.asSubroutine 0 27) frameStoredFinalElement [.halt] 112
    (by change 0 < 84; decide) rfl frameHalt frameStoredFinalElement_control_closed
  change RunsFor prepareMultiplyOperands (restored.resumeAt 27) (framed.resumeAt 112) frameTime at hFrame
  let finish : Configuration := { framed with pc := 112, halted := true }
  have last : Step prepareMultiplyOperands (framed.resumeAt 112) finish := by
    have code : prepareMultiplyOperands[112]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + frameTime + 1, ?_,
    RunsFor.succ (hRestore.trans hFrame) last, rfl, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    omega
  · intro beforeOutput blanks hOutput
    obtain ⟨exactFrame, exactTime, saved, remaining,
      _hTime, exactRun, exactHalt, exactOutput⟩ :=
      frameStoredFinalElement_terminates_with_output_layout restored.inputTape beforeOutput blanks
    have hRestoredOutput : restored.outputTape =
        { left := beforeOutput, right := List.replicate blanks none } := restoreOutput.trans hOutput
    rw [← hRestoredOutput] at exactRun
    have hFrameEq := frameRun.halted_finish_eq_of_no_randomBit exactRun
      frameHalt exactHalt frameStoredFinalElement_no_randomBit
    refine ⟨saved, remaining, ?_⟩
    change framed.outputTape = _
    rw [hFrameEq, exactOutput]

/-- Native operand assembly stops on arbitrary finite caller tapes. Its
stopping bound does not assert successful parsing of an invalid DDH tuple. -/
theorem prepareMultiplyOperands_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000 * (input.cells + output.cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ :=
    prepareMultiplyOperands_terminates_layout_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Operand assembly preserves the fresh output frontier returned by
message preparation, for every finite input tape. Actual stored-input
rewinds preserve the other tape, and final-element framing restores its
frontier even when the public fields or element delimiters are malformed. -/
theorem prepareMultiplyOperands_terminates_with_output_layout (input : Tape)
    (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 1000000000000000000 *
        (input.cells + ({ left := beforeOutput, right := List.replicate blanks none } : Tape).cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input,
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    prepareMultiplyOperands_terminates_layout_core input
      { left := beforeOutput, right := List.replicate blanks none }
  obtain ⟨saved, remaining, hOutput⟩ := hLayout beforeOutput blanks rfl
  exact ⟨finish, used, saved, remaining, hBound, run, hHalted, hOutput⟩


/-- Operand preparation on the four raw blocks actually retained by
message framing. No public-header or tuple validity is assumed. Native
restoration first exposes those blocks; final-element parsing then advances
their input head rightward and preserves its current/right cells through
the temporary delimiter edit. Both stages retain the fresh output frontier. -/
theorem prepareMultiplyOperands_terminates_from_retained_blocks
    (before savedOutput : List (Option Bool))
    (original reply canonical selected : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := restoreInputBeforeScratchStart before original reply canonical selected
      (List.replicate inputBlanks none) output
    let restored := restoreInputBeforeScratchFinish before original reply canonical selected
      (List.replicate inputBlanks none) output
    ∃ finish used saved remaining moves,
      used ≤ 1000000000000000000 * GuardedCompiler.sourceStorage start + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands start finish used ∧ finish.halted = true ∧ moves ≤ used ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      finish.inputTape.current = ((Tape.moveRight^[moves]) restored.inputTape).current ∧
      ∀ i, finish.inputTape.right.getD i none =
        ((Tape.moveRight^[moves]) restored.inputTape).right.getD i none := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start := restoreInputBeforeScratchStart before original reply canonical selected
    (List.replicate inputBlanks none) output
  let restored := restoreInputBeforeScratchFinish before original reply canonical selected
    (List.replicate inputBlanks none) output
  let restoreTime := restoreInputBeforeScratchSteps original reply canonical selected
  have restoreRun := restoreInputBeforeScratch_runs before original reply canonical selected
    (List.replicate inputBlanks none) output
  obtain ⟨framed, frameTime, saved, remaining, moves, hFrameTime,
    frameRun, frameHalt, hMoves, frameOutput, frameCurrent, frameRight⟩ :=
    frameStoredFinalElement_terminates_with_input_output_layout restored.inputTape savedOutput outputBlanks
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreInputBeforeScratch (frameStoredFinalElement.asSubroutine 27 112 ++ [.halt]) 27
    (by change 0 < 26; decide) rfl rfl restoreInputBeforeScratch_control_closed
  change RunsFor prepareMultiplyOperands start (restored.resumeAt 27) restoreTime at hRestore
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (restoreInputBeforeScratch.asSubroutine 0 27) frameStoredFinalElement [.halt] 112
    (by change 0 < 84; decide) rfl frameHalt frameStoredFinalElement_control_closed
  change RunsFor prepareMultiplyOperands (restored.resumeAt 27) (framed.resumeAt 112) frameTime at hFrame
  let finish : Configuration := { framed with pc := 112, halted := true }
  have last : Step prepareMultiplyOperands (framed.resumeAt 112) finish := by
    have code : prepareMultiplyOperands[112]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + frameTime + 1, saved, remaining, moves, ?_,
    RunsFor.succ (hRestore.trans hFrame) last, rfl, by omega, frameOutput, frameCurrent, frameRight⟩
  have hRestoreTime : restoreTime ≤ 2 * GuardedCompiler.sourceStorage start + 21 := by
    dsimp only [restoreTime]
    rw [restoreInputBeforeScratch_steps_eq]
    simp only [GuardedCompiler.sourceStorage, start, restoreInputBeforeScratchStart,
      Tape.cells, List.length_append, List.length_cons, List.length_reverse,
      List.length_map, List.length_replicate]
    omega
  have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
  change restored.inputTape.cells + output.cells ≤ GuardedCompiler.sourceStorage start + restoreTime at hStorage
  change frameTime ≤ 1000000000000 * (restored.inputTape.cells + output.cells) + 1000000000000 at hFrameTime
  change restoreTime + frameTime + 1 ≤
    1000000000000000000 * GuardedCompiler.sourceStorage start + 1000000000000000000
  omega

/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem prepareMultiplyOperands_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareMultiplyOperands
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000000000000 * (input.cells + output.cells) + 1000000000000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    prepareMultiplyOperands_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareMultiplyOperands_no_randomBit hBound finish trace

/-- The arbitrary-raw message stage returns exactly the four-block input
layout accepted by the next native restoration. A contiguous original
prefix already behind the head is joined to its remaining bits by list
identity only. No DDH parser, normalization correctness, or fresh load is
used; the returned output retains its actual assembled request frontier. -/
theorem prepareMultiplyMessage_terminates_with_restoration_layout
    (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before)
      original reply canonical inputBlanks output
    ∃ finish used, ∃ (selected : List Bool), ∃ remainingInput afterOutput remainingOutput,
      used ≤ 200000000 * GuardedCompiler.sourceStorage start + 200000000 ∧
      RunsFor prepareMultiplyMessage start finish used ∧ finish.halted = true ∧
      finish.resumeAt 0 = restoreInputBeforeScratchStart before (originalPrefix ++ original)
        reply canonical selected (List.replicate remainingInput none)
        { left := afterOutput, right := List.replicate remainingOutput none } := by
  dsimp only
  obtain ⟨finish, used, selected, remainingInput, afterOutput, remainingOutput,
    hBound, run, hHalted, hInput, hOutput⟩ :=
    prepareMultiplyMessage_terminates_with_retained_frontiers
      (originalPrefix.reverse.map some ++ none :: before) savedOutput
      original reply canonical inputBlanks outputBlanks
  refine ⟨finish, used, selected, remainingInput, afterOutput, remainingOutput,
    hBound, run, hHalted, ?_⟩
  simp only [Configuration.resumeAt, restoreInputBeforeScratchStart, hInput, hOutput,
    List.reverse_append, List.map_append, List.append_assoc, List.cons_append]

/-- Both native preparation stages execute on the same physical caller
tapes. The message-stage return is resumed directly by operand assembly,
including arbitrary raw original and reply blocks. Their combined overhead
has one storage bound and their actual final output has a blank frontier.
This statement does not assert that the input head is yet ready for a call. -/
theorem prepareMultiplyMessage_operands_terminate_with_output_layout
    (before savedOutput : List (Option Bool))
    (original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart before original reply canonical inputBlanks output
    ∃ messageFinish operandFinish messageTime operandTime saved remaining,
      messageTime + operandTime ≤
        1000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
        1000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧
      messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start := seekStoredInputScratchStart before original reply canonical inputBlanks output
  obtain ⟨messageFinish, messageTime, _selected, _inputRemaining, messageOutput, messageBlanks,
    hMessageTime, messageRun, messageHalt, _messageInput, hMessageOutput⟩ :=
    prepareMultiplyMessage_terminates_with_retained_frontiers
      before savedOutput original reply canonical inputBlanks outputBlanks
  obtain ⟨operandFinish, operandTime, saved, remaining,
    hOperandTime, operandRun, operandHalt, hOperandOutput⟩ :=
    prepareMultiplyOperands_terminates_with_output_layout messageFinish.inputTape messageOutput messageBlanks
  rw [← hMessageOutput] at operandRun hOperandTime
  change RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime at operandRun
  refine ⟨messageFinish, operandFinish, messageTime, operandTime, saved, remaining, ?_,
    messageRun, messageHalt, operandRun, operandHalt, hOperandOutput⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run messageRun
  change GuardedCompiler.sourceStorage messageFinish ≤ GuardedCompiler.sourceStorage start + messageTime at hStorage
  change messageTime ≤ 200000000 * GuardedCompiler.sourceStorage start + 200000000 at hMessageTime
  change operandTime ≤ 1000000000000000000 * GuardedCompiler.sourceStorage messageFinish +
    1000000000000000000 at hOperandTime
  change messageTime + operandTime ≤
    1000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
    1000000000000000000000000000000
  omega

/-- The actual arbitrary-raw message return feeds operand assembly with
its four retained blocks. The final input cells are a rightward suffix of
the restored original/reply/canonical/selected layout. This supplies the
remaining-input invariant for the following four native call-preparation
scans without assuming that the original DDH input parses successfully. -/
theorem prepareMultiplyMessage_operands_terminate_with_input_output_layout
    (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before)
      original reply canonical inputBlanks output
    ∃ messageFinish operandFinish messageTime operandTime saved remaining moves,
      ∃ (selected : List Bool) (remainingInput : Nat),
      let restored := restoreInputBeforeScratchFinish before (originalPrefix ++ original)
        reply canonical selected (List.replicate remainingInput none) {}
      messageTime + operandTime ≤
        1000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
        1000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧
      messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧ moves ≤ operandTime ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      operandFinish.inputTape.current = ((Tape.moveRight^[moves]) restored.inputTape).current ∧
      ∀ i, operandFinish.inputTape.right.getD i none =
        ((Tape.moveRight^[moves]) restored.inputTape).right.getD i none := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start := seekStoredInputScratchStart
    (originalPrefix.reverse.map some ++ none :: before)
    original reply canonical inputBlanks output
  obtain ⟨messageFinish, messageTime, selected, remainingInput, messageOutput, messageBlanks,
    hMessageTime, messageRun, messageHalt, hMessageEntry⟩ :=
    prepareMultiplyMessage_terminates_with_restoration_layout
      before savedOutput originalPrefix original reply canonical inputBlanks outputBlanks
  obtain ⟨operandFinish, operandTime, saved, remaining, moves,
    hOperandTime, operandRun, operandHalt, hMoves, hOutput, hCurrent, hRight⟩ :=
    prepareMultiplyOperands_terminates_from_retained_blocks before messageOutput
      (originalPrefix ++ original) reply canonical selected remainingInput messageBlanks
  rw [← hMessageEntry] at operandRun hOperandTime
  have hStorage := GuardedCompiler.sourceStorage_le_of_run messageRun
  change GuardedCompiler.sourceStorage messageFinish ≤ GuardedCompiler.sourceStorage start + messageTime at hStorage
  change messageTime ≤ 200000000 * GuardedCompiler.sourceStorage start + 200000000 at hMessageTime
  change operandTime ≤ 1000000000000000000 * GuardedCompiler.sourceStorage messageFinish +
    1000000000000000000 at hOperandTime
  refine ⟨messageFinish, operandFinish, messageTime, operandTime, saved, remaining,
    moves, selected, remainingInput, ?_, messageRun, messageHalt, operandRun,
    operandHalt, hMoves, hOutput, hCurrent, hRight⟩
  change messageTime + operandTime ≤
    1000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
    1000000000000000000000000000000
  omega

end Machine
