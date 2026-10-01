import Foundation.Machine.ContextualInput
import Foundation.Machine.DelimitedSkip
import Foundation.Machine.FrameAfterDelimiter

namespace Machine

open FiniteBitEncoding

/-- Append the raw last component of a stored encoded DDH tuple to an
existing arithmetic request. The public parameter and instance are scanned,
then the outer tuple header and its two delimited components. Framing the
last component temporarily changes and restores one known false delimiter. -/
def frameStoredFinalElement : Program :=
  skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
  skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
  skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]

private def delimiterBody (bits : List Bool) : List Bool :=
  bits.flatMap (fun bit => [true, bit])

private theorem delimit_eq_body (bits : List Bool) :
    delimit bits = delimiterBody bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simpa [delimit, delimiterBody] using congrArg (fun xs => true :: bit :: xs) ih

private def storedTupleBits (first second last : List Bool) : List Bool :=
  delimit first ++ delimit second ++ last

private def beforeStoredLast (beforeInput : List (Option Bool)) (n : Nat)
    (instanceBits first second last : List Bool) : List (Option Bool) :=
  (delimiterBody second).reverse.map some ++ (delimit first).reverse.map some ++
    (encodeSecurityParameter (storedTupleBits first second last).length).reverse.map some ++
    (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput

def frameStoredFinalElementStart (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) : Configuration :=
  skipUnaryCellsStart (none :: beforeInput) n
    ((frame instanceBits ++ frame (storedTupleBits first second last)).map some ++ none :: tail)
    { left := beforeOutput }

def frameStoredFinalElementFinish (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) : Configuration :=
  { writeFrameAfterFalseFinish (beforeStoredLast beforeInput n instanceBits first second last)
      beforeOutput tail last (instanceBits.length + 1) with pc := 83 }

def frameStoredFinalElementSteps (n : Nat) (instanceBits first second last : List Bool) : Nat :=
  (3 * n + 3) + 1 + (10 * instanceBits.length + 5) +
    (3 * (storedTupleBits first second last).length + 3) +
    (4 * first.length + 3) + (4 * second.length + 3) + writeFrameAfterFalseSteps last + 1

set_option maxHeartbeats 1200000 in
theorem frameStoredFinalElement_runs (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    RunsFor frameStoredFinalElement
      (frameStoredFinalElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last)
      (frameStoredFinalElementSteps n instanceBits first second last) := by
  let tuple := storedTupleBits first second last
  let tupleCells := (frame tuple).map some ++ none :: tail
  let instanceCells := instanceBits.map some ++ tupleCells
  let output : Tape := { left := beforeOutput }
  let beforeInstance := (encodeSecurityParameter n).reverse.map some ++ none :: beforeInput
  let beforeTuple := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput
  let counterOutput : Tape := { left := beforeOutput, right := List.replicate (instanceBits.length + 1) none }
  let beforeFirst := (encodeSecurityParameter tuple.length).reverse.map some ++ beforeTuple
  let beforeSecond := (delimit first).reverse.map some ++ beforeFirst
  let tailFirst := (delimit second ++ last).map some ++ none :: tail
  let tailSecond := last.map some ++ none :: tail
  let unaryFinish := skipUnaryCellsFinish (none :: beforeInput) n ((frame instanceBits).map some ++ tupleCells) output
  have hUnary := (skipUnaryCells_runs (none :: beforeInput) n
      ((frame instanceBits).map some ++ tupleCells) output).withSubroutine_halted_of_closed
    [] skipUnary ([.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 7
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  have hUnary' : RunsFor frameStoredFinalElement
      (frameStoredFinalElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (unaryFinish.resumeAt 7) (3 * n + 3) := by
    simpa [frameStoredFinalElement, frameStoredFinalElementStart, tupleCells,
      unaryFinish, tuple, Program.withSubroutine, Configuration.rebasePc,
      List.map_append, List.append_assoc] using hUnary
  let instanceStart := skipFrameCellsStart beforeInstance beforeOutput instanceBits.length instanceCells
  have hReserve : Step frameStoredFinalElement (unaryFinish.resumeAt 7) (instanceStart.rebasePc 8) := by
    cases instanceBits <;> simp [Step, successors, next, frameStoredFinalElement, skipUnary,
      Program.asSubroutine, Instruction.asSubroutine, unaryFinish, skipUnaryCellsFinish_layout,
      instanceStart, skipFrameCellsStart_layout, instanceCells, beforeInstance, encodeSecurityParameter, frame,
      output, Configuration.resumeAt, Configuration.rebasePc, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveRight,
      List.map_append, List.map_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ]
  have hInstance := (skipFrameCells_runs beforeInstance beforeOutput instanceBits.length instanceCells).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output]) skipFrame
    (skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 22
    (by change 0 < 13; decide) rfl rfl skipFrame_control_closed
  change RunsFor frameStoredFinalElement (instanceStart.rebasePc 8)
    ((skipFrameCellsFinish beforeInstance beforeOutput instanceBits.length instanceCells).resumeAt 22)
    (10 * instanceBits.length + 5) at hInstance
  let tupleStart := skipUnaryCellsStart beforeTuple tuple.length (tuple.map some ++ none :: tail) counterOutput
  have hTupleStart : (skipFrameCellsFinish beforeInstance beforeOutput instanceBits.length instanceCells).resumeAt 22 =
      tupleStart.rebasePc 22 := by
    have hInput := skipFrameCellsFinish_input beforeInstance beforeOutput instanceBits
      (some false) (tuple.map some ++ none :: tail)
    -- The outer header is nonempty precisely when the tuple payload is.
    have hInput' : (skipFrameCellsFinish beforeInstance beforeOutput instanceBits.length instanceCells).inputTape =
        { ({ right := (frame tuple).map some ++ none :: tail } : Tape).moveRight with
          left := (frame instanceBits).reverse.map some ++ beforeInstance } := by
      cases hCount : tuple.length with
      | zero =>
          simpa [instanceCells, tupleCells, frame, hCount, Tape.moveRight, List.reverse_append,
            List.map_append, List.reverse_replicate] using hInput
      | succ count =>
          have h := skipFrameCellsFinish_input beforeInstance beforeOutput instanceBits
            (some true) (List.replicate count (some true) ++ some false :: tuple.map some ++ none :: tail)
          simpa [instanceCells, tupleCells, frame, hCount, Tape.moveRight, List.map_append,
            List.map_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ] using h
    change ({
        pc := 22
        inputTape := (skipFrameCellsFinish beforeInstance beforeOutput instanceBits.length instanceCells).inputTape
        outputTape := counterOutput } : Configuration) = tupleStart.rebasePc 22
    rw [hInput']
    simp [tupleStart, skipUnaryCellsStart_layout, beforeTuple, beforeInstance,
      counterOutput, Configuration.rebasePc, encodeSecurityParameter, frame,
      List.reverse_append, List.map_append, List.map_replicate, List.reverse_replicate,
      List.append_assoc]
  rw [hTupleStart] at hInstance
  have hTuple := (skipUnaryCells_runs beforeTuple tuple.length (tuple.map some ++ none :: tail) counterOutput).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22) skipUnary
    (skipDelimited.asSubroutine 29 37 ++ skipDelimited.asSubroutine 37 45 ++
      writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 29
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  change RunsFor frameStoredFinalElement (tupleStart.rebasePc 22)
    ((skipUnaryCellsFinish beforeTuple tuple.length (tuple.map some ++ none :: tail) counterOutput).resumeAt 29)
    (3 * tuple.length + 3) at hTuple
  let firstStart := skipDelimitedStart beforeFirst first tailFirst counterOutput
  have hFirstStart : (skipUnaryCellsFinish beforeTuple tuple.length (tuple.map some ++ none :: tail) counterOutput).resumeAt 29 =
      firstStart.rebasePc 29 := by
    cases first <;> simp [tuple, storedTupleBits, delimit, skipUnaryCellsFinish_layout,
      firstStart, skipDelimitedStart_layout, beforeFirst, tailFirst,
      Configuration.resumeAt, Configuration.rebasePc, encodeSecurityParameter, Tape.moveRight,
      List.map_append, List.append_assoc, List.reverse_append, List.reverse_replicate, List.map_replicate]
  rw [hFirstStart] at hTuple
  have hFirst := (skipDelimited_runs beforeFirst first tailFirst counterOutput).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++ skipUnary.asSubroutine 22 29)
    skipDelimited (skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 37
    (by change 0 < 7; decide) rfl rfl skipDelimited_control_closed
  change RunsFor frameStoredFinalElement (firstStart.rebasePc 29)
    ((skipDelimitedFinish beforeFirst first tailFirst counterOutput).resumeAt 37)
    (4 * first.length + 3) at hFirst
  let secondStart := skipDelimitedStart beforeSecond second tailSecond counterOutput
  have hSecondStart : (skipDelimitedFinish beforeFirst first tailFirst counterOutput).resumeAt 37 =
      secondStart.rebasePc 37 := by
    cases second <;> simp [skipDelimitedFinish_layout, secondStart, skipDelimitedStart_layout,
      beforeSecond, tailFirst, tailSecond, delimit, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight, List.map_append, List.append_assoc]
  rw [hSecondStart] at hFirst
  have hSecond := (skipDelimited_runs beforeSecond second tailSecond counterOutput).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37)
    skipDelimited (writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 45
    (by change 0 < 7; decide) rfl rfl skipDelimited_control_closed
  change RunsFor frameStoredFinalElement (secondStart.rebasePc 37)
    ((skipDelimitedFinish beforeSecond second tailSecond counterOutput).resumeAt 45)
    (4 * second.length + 3) at hSecond
  let frameStart := writeFrameAfterFalseStart (beforeStoredLast beforeInput n instanceBits first second last)
    beforeOutput tail last (instanceBits.length + 1)
  have hLastStart : (skipDelimitedFinish beforeSecond second tailSecond counterOutput).resumeAt 45 =
      frameStart.rebasePc 45 := by
    cases last <;> simp [skipDelimitedFinish_layout, frameStart, writeFrameAfterFalseStart_layout,
      beforeStoredLast, beforeSecond, beforeFirst, beforeTuple, tuple, tailSecond,
      counterOutput, delimit_eq_body second, List.reverse_append, List.map_append,
      Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight, List.append_assoc]
  rw [hLastStart] at hSecond
  have hFrame := (writeFrameAfterFalse_runs (beforeStoredLast beforeInput n instanceBits first second last)
      beforeOutput tail last (instanceBits.length + 1)).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++ skipDelimited.asSubroutine 37 45)
    writeFrameAfterFalse [.halt] 83 (by change 0 < 37; decide) rfl rfl writeFrameAfterFalse_control_closed
  change RunsFor frameStoredFinalElement (frameStart.rebasePc 45)
    ((frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last).resumeAt 83)
    (writeFrameAfterFalseSteps last) at hFrame
  have hHalt : Step frameStoredFinalElement
      ((frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last).resumeAt 83)
      (frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last) := by
    simp [Step, successors, next, frameStoredFinalElement, skipUnary, skipFrame, skipDelimited,
      writeFrameAfterFalse, writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, frameStoredFinalElementFinish,
      writeFrameAfterFalseFinish, Configuration.resumeAt, Instruction.next]
  have run := RunsFor.succ (((((RunsFor.succ hUnary' hReserve).trans hInstance).trans hTuple).trans hFirst).trans hSecond |>.trans hFrame) hHalt
  simpa only [frameStoredFinalElementSteps, tuple] using run

theorem frameStoredFinalElement_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ frameStoredFinalElement := by
  simp [frameStoredFinalElement, skipUnary, skipFrame, skipDelimited, writeFrameAfterFalse,
    writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem frameStoredFinalElement_eval (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    evalConfigWithin frameStoredFinalElement
      (frameStoredFinalElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (frameStoredFinalElementSteps n instanceBits first second last) =
      PMF.pure (frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last) :=
  (frameStoredFinalElement_runs beforeInput beforeOutput tail n instanceBits first second last).evalConfigWithin_eq_pure_of_no_randomBit
    frameStoredFinalElement_no_randomBit

/-- Payload-first order agrees with the represented group multiplication
input; this routine never changes the operand to a commuted product. -/
theorem frameStoredFinalElementFinish_output (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    (frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last).outputTape =
      { left := (frame last).reverse.map some ++ beforeOutput,
        right := List.replicate (instanceBits.length + 1 - (2 * last.length + 1)) none } := rfl

theorem frameStoredFinalElement_steps_le (n : Nat) (instanceBits first second last : List Bool) :
    frameStoredFinalElementSteps n instanceBits first second last ≤
      3 * n + 10 * instanceBits.length + 10 * (first.length + second.length) + 18 * last.length + 47 := by
  have h := writeFrameAfterFalse_steps_le last
  simp only [frameStoredFinalElementSteps, storedTupleBits, List.length_append,
    FiniteBitEncoding.delimit_length]
  omega

theorem frameStoredFinalElementFinish_input (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    (frameStoredFinalElementFinish beforeInput beforeOutput tail n instanceBits first second last).inputTape =
      { ({ right := last.map some ++ none :: tail } : Tape).moveRight with
        left := (delimit second).reverse.map some ++ (delimit first).reverse.map some ++
          (encodeSecurityParameter (delimit first ++ delimit second ++ last).length).reverse.map some ++
          (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput } := by
  simp only [frameStoredFinalElementFinish]
  rw [writeFrameAfterFalseFinish_input]
  simp [beforeStoredLast, storedTupleBits, delimit_eq_body second, List.reverse_append,
    List.map_append, List.append_assoc]

theorem frameStoredFinalElementStart_layout (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    frameStoredFinalElementStart beforeInput beforeOutput tail n instanceBits first second last =
      { inputTape := { ({ right :=
            (encodeSecurityParameter n ++ frame instanceBits ++ frame (delimit first ++ delimit second ++ last)).map some ++
              none :: tail } : Tape).moveRight with left := none :: beforeInput },
        outputTape := { left := beforeOutput } } := by
  cases n <;> simp [frameStoredFinalElementStart, skipUnaryCellsStart_layout, storedTupleBits,
    encodeSecurityParameter, List.map_append, List.map_replicate, List.replicate_succ,
    Tape.moveRight, List.append_assoc]

set_option maxHeartbeats 2000000 in
theorem frameStoredFinalElement_control_closed (c d : Configuration)
    (hPc : c.pc < frameStoredFinalElement.length) (step : Step frameStoredFinalElement c d)
    (_hRunning : d.halted = false) : d.pc < frameStoredFinalElement.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 84 at hPc
  change d.pc < 84
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, frameStoredFinalElement,
    skipUnary, skipFrame, skipDelimited, writeFrameAfterFalse, writeFrame, writeFrameHeader,
    rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


/-- The complete last-element preparation stops on every finite retained
configuration, even if the tuple fields or the scratch counter are malformed.
All scans and writes are the existing native subroutines, with no data reset. -/
theorem frameStoredFinalElement_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000 ∧
      RunsFor frameStoredFinalElement
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨publicFinish, a, ha, publicRun, publicHalt, _publicOutput⟩ :=
    skipUnary_terminates_from_anyTape input output
  have hPublic := publicRun.withSubroutine_halted_of_closed
    [] skipUnary
    ([.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++ skipUnary.asSubroutine 22 29 ++
      skipDelimited.asSubroutine 29 37 ++ skipDelimited.asSubroutine 37 45 ++
      writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 7
    (by change 0 < 6; decide) rfl publicHalt skipUnary_control_closed
  change RunsFor frameStoredFinalElement
    ({ inputTape := input, outputTape := output } : Configuration) (publicFinish.resumeAt 7) a at hPublic
  let frameStart : Configuration :=
    { pc := 8, inputTape := publicFinish.inputTape, outputTape := publicFinish.outputTape.moveRight }
  have advance : Step frameStoredFinalElement (publicFinish.resumeAt 7) frameStart := by
    have code : frameStoredFinalElement[7]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, frameStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toFrame := RunsFor.succ hPublic advance
  obtain ⟨frameFinish, b, hb, frameRun, frameHalt⟩ :=
    skipFrame_terminates_from_anyTape frameStart.inputTape frameStart.outputTape
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output]) skipFrame
    (skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 22
    (by change 0 < 13; decide) rfl frameHalt skipFrame_control_closed
  change RunsFor frameStoredFinalElement frameStart (frameFinish.resumeAt 22) b at hFrame
  have toTuple := toFrame.trans hFrame
  obtain ⟨tupleFinish, c, hc, tupleRun, tupleHalt, _tupleOutput⟩ :=
    skipUnary_terminates_from_anyTape frameFinish.inputTape frameFinish.outputTape
  have hTuple := tupleRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22) skipUnary
    (skipDelimited.asSubroutine 29 37 ++ skipDelimited.asSubroutine 37 45 ++
      writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 29
    (by change 0 < 6; decide) rfl tupleHalt skipUnary_control_closed
  change RunsFor frameStoredFinalElement (frameFinish.resumeAt 22) (tupleFinish.resumeAt 29) c at hTuple
  have toFirst := toTuple.trans hTuple
  obtain ⟨firstFinish, d, hd, firstRun, firstHalt, _firstOutput⟩ :=
    skipDelimited_terminates_from_anyTape tupleFinish.inputTape tupleFinish.outputTape
  have hFirst := firstRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29) skipDelimited
    (skipDelimited.asSubroutine 37 45 ++ writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 37
    (by change 0 < 7; decide) rfl firstHalt skipDelimited_control_closed
  change RunsFor frameStoredFinalElement (tupleFinish.resumeAt 29) (firstFinish.resumeAt 37) d at hFirst
  have toSecond := toFirst.trans hFirst
  obtain ⟨secondFinish, e, he, secondRun, secondHalt, _secondOutput⟩ :=
    skipDelimited_terminates_from_anyTape firstFinish.inputTape firstFinish.outputTape
  have hSecond := secondRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37) skipDelimited
    (writeFrameAfterFalse.asSubroutine 45 83 ++ [.halt]) 45
    (by change 0 < 7; decide) rfl secondHalt skipDelimited_control_closed
  change RunsFor frameStoredFinalElement (firstFinish.resumeAt 37) (secondFinish.resumeAt 45) e at hSecond
  have toLast := toSecond.trans hSecond
  obtain ⟨framed, f, hf, lastRun, lastHalt⟩ :=
    writeFrameAfterFalse_terminates_from_anyTape secondFinish.inputTape secondFinish.outputTape
  have hLast := lastRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      skipDelimited.asSubroutine 37 45) writeFrameAfterFalse [.halt] 83
    (by change 0 < 37; decide) rfl lastHalt writeFrameAfterFalse_control_closed
  change RunsFor frameStoredFinalElement (secondFinish.resumeAt 45) (framed.resumeAt 83) f at hLast
  let finish : Configuration := { framed with pc := 83, halted := true }
  have last : Step frameStoredFinalElement (framed.resumeAt 83) finish := by
    have code : frameStoredFinalElement[83]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, a + 1 + b + c + d + e + f + 1, ?_, RunsFor.succ (toLast.trans hLast) last, rfl⟩
  have frameStorage := GuardedCompiler.sourceStorage_le_of_run toFrame
  change frameStart.inputTape.cells + frameStart.outputTape.cells ≤ input.cells + output.cells + (a + 1) at frameStorage
  have tupleStorage := GuardedCompiler.sourceStorage_le_of_run toTuple
  change frameFinish.inputTape.cells + frameFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b) at tupleStorage
  have firstStorage := GuardedCompiler.sourceStorage_le_of_run toFirst
  change tupleFinish.inputTape.cells + tupleFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b + c) at firstStorage
  have secondStorage := GuardedCompiler.sourceStorage_le_of_run toSecond
  change firstFinish.inputTape.cells + firstFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b + c + d) at secondStorage
  have lastStorage := GuardedCompiler.sourceStorage_le_of_run toLast
  change secondFinish.inputTape.cells + secondFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b + c + d + e) at lastStorage
  omega

end Machine
