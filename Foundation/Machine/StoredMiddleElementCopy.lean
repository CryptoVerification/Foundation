import Foundation.Machine.ContextualInput
import Foundation.Machine.DelimitedSkip
import Foundation.Machine.DelimitedCopy

namespace Machine

open FiniteBitEncoding

private def storedTupleBits (first second last : List Bool) : List Bool :=
  delimit first ++ delimit second ++ last

/-- Append the second delimited component of a retained DDH tuple to the
current guess-request body. The public prefix, outer frame, and first field
are scanned by native instructions. The copied field is the ciphertext's
first component; the original tuple and all following caller cells survive. -/
def copyStoredMiddleElement : Program :=
  skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
    skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
    copyDelimited.asSubroutine 37 53 ++ [.halt]

def copyStoredMiddleElementStart (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) : Configuration :=
  skipUnaryCellsStart (none :: beforeInput) n
    ((frame instanceBits ++ frame (storedTupleBits first second last)).map some ++ none :: tail)
    { left := beforeOutput }

def copyStoredMiddleElementFinish (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) : Configuration :=
  { copyDelimitedFinish
      ((delimit first).reverse.map some ++
        (encodeSecurityParameter (storedTupleBits first second last).length).reverse.map some ++
        (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput)
      beforeOutput (last.map some ++ none :: tail) second (instanceBits.length + 1) with pc := 53 }

def copyStoredMiddleElementSteps (n : Nat) (instanceBits first second last : List Bool) : Nat :=
  (3*n + 3) + 1 + (10*instanceBits.length + 5) +
    (3*(storedTupleBits first second last).length + 3) + (4*first.length + 3) +
    copyDelimitedSteps second + 1

set_option maxHeartbeats 1200000 in
theorem copyStoredMiddleElement_runs (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    RunsFor copyStoredMiddleElement
      (copyStoredMiddleElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last)
      (copyStoredMiddleElementSteps n instanceBits first second last) := by
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
      copyDelimited.asSubroutine 37 53 ++ [.halt]) 7
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  have hUnary' : RunsFor copyStoredMiddleElement
      (copyStoredMiddleElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (unaryFinish.resumeAt 7) (3 * n + 3) := by
    simpa [copyStoredMiddleElement, copyStoredMiddleElementStart, tupleCells,
      unaryFinish, tuple, Program.withSubroutine, Configuration.rebasePc,
      List.map_append, List.append_assoc] using hUnary
  let instanceStart := skipFrameCellsStart beforeInstance beforeOutput instanceBits.length instanceCells
  have hReserve : Step copyStoredMiddleElement (unaryFinish.resumeAt 7) (instanceStart.rebasePc 8) := by
    cases instanceBits <;> simp [Step, successors, next, copyStoredMiddleElement, skipUnary,
      Program.asSubroutine, Instruction.asSubroutine, unaryFinish, skipUnaryCellsFinish_layout,
      instanceStart, skipFrameCellsStart_layout, instanceCells, beforeInstance, encodeSecurityParameter, frame,
      output, Configuration.resumeAt, Configuration.rebasePc, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveRight,
      List.map_append, List.map_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ]
  have hInstance := (skipFrameCells_runs beforeInstance beforeOutput instanceBits.length instanceCells).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output]) skipFrame
    (skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      copyDelimited.asSubroutine 37 53 ++ [.halt]) 22
    (by change 0 < 13; decide) rfl rfl skipFrame_control_closed
  change RunsFor copyStoredMiddleElement (instanceStart.rebasePc 8)
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
    (skipDelimited.asSubroutine 29 37 ++ copyDelimited.asSubroutine 37 53 ++ [.halt]) 29
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  change RunsFor copyStoredMiddleElement (tupleStart.rebasePc 22)
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
    skipDelimited (copyDelimited.asSubroutine 37 53 ++ [.halt]) 37
    (by change 0 < 7; decide) rfl rfl skipDelimited_control_closed
  change RunsFor copyStoredMiddleElement (firstStart.rebasePc 29)
    ((skipDelimitedFinish beforeFirst first tailFirst counterOutput).resumeAt 37)
    (4 * first.length + 3) at hFirst
  let copyStart := copyDelimitedStart beforeSecond beforeOutput tailSecond second (instanceBits.length + 1)
  have hCopyStart : (skipDelimitedFinish beforeFirst first tailFirst counterOutput).resumeAt 37 =
      copyStart.rebasePc 37 := by
    cases second <;> simp [skipDelimitedFinish_layout_cells, copyStart, copyDelimitedStart_layout,
      beforeSecond, tailFirst, tailSecond, counterOutput, delimit, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight, List.map_append, List.append_assoc]
  rw [hCopyStart] at hFirst
  have hCopy := (copyDelimited_runs beforeSecond beforeOutput tailSecond second (instanceBits.length + 1)).withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37)
    copyDelimited [.halt] 53 (by change 0 < 15; decide) rfl rfl copyDelimited_control_closed
  have hCopyFinish : copyDelimitedFinish beforeSecond beforeOutput tailSecond second (instanceBits.length + 1) =
      { copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last with pc := 14 } := by
    simp [copyStoredMiddleElementFinish, copyDelimitedFinish, beforeSecond, beforeFirst, beforeTuple,
      tuple, tailSecond, List.append_assoc]
  rw [hCopyFinish] at hCopy
  change RunsFor copyStoredMiddleElement (copyStart.rebasePc 37)
    ((copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last).resumeAt 53)
    (copyDelimitedSteps second) at hCopy
  have hHalt : Step copyStoredMiddleElement
      ((copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last).resumeAt 53)
      (copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last) := by
    simp [Step, successors, next, copyStoredMiddleElement, skipUnary, skipFrame, skipDelimited,
      copyDelimited, Program.asSubroutine, Instruction.asSubroutine, copyStoredMiddleElementFinish,
      copyDelimitedFinish, Configuration.resumeAt, Instruction.next]
  have run := RunsFor.succ (((((RunsFor.succ hUnary' hReserve).trans hInstance).trans hTuple).trans hFirst).trans hCopy) hHalt
  simpa only [copyStoredMiddleElementSteps, tuple] using run

theorem copyStoredMiddleElement_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyStoredMiddleElement := by
  simp [copyStoredMiddleElement, skipUnary, skipFrame, skipDelimited, copyDelimited,
    Program.asSubroutine, Instruction.asSubroutine]

theorem copyStoredMiddleElement_eval (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    evalConfigWithin copyStoredMiddleElement
      (copyStoredMiddleElementStart beforeInput beforeOutput tail n instanceBits first second last)
      (copyStoredMiddleElementSteps n instanceBits first second last) =
      PMF.pure (copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last) :=
  (copyStoredMiddleElement_runs _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit
    copyStoredMiddleElement_no_randomBit

theorem copyStoredMiddleElement_steps_le (n : Nat) (instanceBits first second last : List Bool) :
    copyStoredMiddleElementSteps n instanceBits first second last ≤
      3*n + 10*instanceBits.length + 10*first.length + 16*second.length + 3*last.length + 27 := by
  have h := copyDelimited_steps_le second
  simp only [copyStoredMiddleElementSteps, storedTupleBits, List.length_append, delimit_length]
  omega

theorem copyStoredMiddleElementFinish_output (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    (copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last).outputTape =
      { left := (delimit second).reverse.map some ++ beforeOutput,
        right := List.replicate (instanceBits.length + 1 - (2*second.length + 1)) none } := rfl

theorem copyStoredMiddleElementFinish_input (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    (copyStoredMiddleElementFinish beforeInput beforeOutput tail n instanceBits first second last).inputTape =
      { ({ right := last.map some ++ none :: tail } : Tape).moveRight with
        left := (delimit second).reverse.map some ++ (delimit first).reverse.map some ++
          (encodeSecurityParameter (delimit first ++ delimit second ++ last).length).reverse.map some ++
          (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: beforeInput } := by
  simp [copyStoredMiddleElementFinish, copyDelimitedFinish_layout, storedTupleBits, List.append_assoc]

theorem copyStoredMiddleElementStart_layout (beforeInput beforeOutput tail : List (Option Bool))
    (n : Nat) (instanceBits first second last : List Bool) :
    copyStoredMiddleElementStart beforeInput beforeOutput tail n instanceBits first second last =
      { inputTape := { ({ right :=
            (encodeSecurityParameter n ++ frame instanceBits ++ frame (delimit first ++ delimit second ++ last)).map some ++
              none :: tail } : Tape).moveRight with left := none :: beforeInput },
        outputTape := { left := beforeOutput } } := by
  cases n <;> simp [copyStoredMiddleElementStart, skipUnaryCellsStart_layout, storedTupleBits,
    encodeSecurityParameter, List.map_append, List.map_replicate, List.replicate_succ,
    Tape.moveRight, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem copyStoredMiddleElement_control_closed (c d : Configuration)
    (hPc : c.pc < copyStoredMiddleElement.length) (step : Step copyStoredMiddleElement c d)
    (_hRunning : d.halted = false) : d.pc < copyStoredMiddleElement.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 54 at hPc
  change d.pc < 54
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, copyStoredMiddleElement,
    skipUnary, skipFrame, skipDelimited, copyDelimited, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
