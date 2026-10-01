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
theorem prepareMultiplyOperands_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000 * (input.cells + output.cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, _restoreOutput⟩ :=
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
  refine ⟨finish, restoreTime + frameTime + 1, ?_, RunsFor.succ (hRestore.trans hFrame) last, rfl⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
  change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
  omega

end Machine
