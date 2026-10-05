import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.DelimitedSkip
import Foundation.Crypto.Semantics.Machine.DelimitedCopy
import Foundation.Crypto.Semantics.Machine.GuardedTrace

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


set_option maxHeartbeats 1200000 in
/-- The public-field scans and middle-field copy preserve every input cell.
Their input head only advances, including on malformed encodings, and each
advance is charged to a native transition in the supplied trace. -/
theorem copyStoredMiddleElement_input_position {start finish : Configuration} {used : Nat}
    (run : RunsFor copyStoredMiddleElement start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape := by
  apply run.input_moveRight_of_step
  intro c d step
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  by_cases hPc : c.pc < 54
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, copyStoredMiddleElement,
      skipUnary, skipFrame, skipDelimited, copyDelimited, Program.asSubroutine,
      Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : copyStoredMiddleElement[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 54 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

/-- Public/tuple scanning and middle-field copying stop on arbitrary finite
caller tapes. A malformed field can yield a partial copy, but its native
marker/payload loop still has a bound in the actual retained storage. -/
private theorem copyStoredMiddleElement_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor copyStoredMiddleElement
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∃ count, finish.inputTape.right = input.right.drop count) ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨publicFinish, a, ha, publicRun, publicHalt, publicOutput⟩ :=
    skipUnary_terminates_from_anyTape input output
  have hPublic := publicRun.withSubroutine_halted_of_closed
    [] skipUnary
    ([.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++ skipUnary.asSubroutine 22 29 ++
      skipDelimited.asSubroutine 29 37 ++ copyDelimited.asSubroutine 37 53 ++ [.halt]) 7
    (by change 0 < 6; decide) rfl publicHalt skipUnary_control_closed
  change RunsFor copyStoredMiddleElement
    ({ inputTape := input, outputTape := output } : Configuration) (publicFinish.resumeAt 7) a at hPublic
  let frameStart : Configuration :=
    { pc := 8, inputTape := publicFinish.inputTape, outputTape := publicFinish.outputTape.moveRight }
  have advance : Step copyStoredMiddleElement (publicFinish.resumeAt 7) frameStart := by
    have code : copyStoredMiddleElement[7]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, frameStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toFrame := RunsFor.succ hPublic advance
  obtain ⟨frameFinish, b, hb, frameRun, frameHalt⟩ :=
    skipFrame_terminates_from_anyTape frameStart.inputTape frameStart.outputTape
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output]) skipFrame
    (skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37 ++
      copyDelimited.asSubroutine 37 53 ++ [.halt]) 22
    (by change 0 < 13; decide) rfl frameHalt skipFrame_control_closed
  change RunsFor copyStoredMiddleElement frameStart (frameFinish.resumeAt 22) b at hFrame
  have toTuple := toFrame.trans hFrame
  obtain ⟨tupleFinish, c, hc, tupleRun, tupleHalt, tupleOutput⟩ :=
    skipUnary_terminates_from_anyTape frameFinish.inputTape frameFinish.outputTape
  have hTuple := tupleRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22) skipUnary
    (skipDelimited.asSubroutine 29 37 ++ copyDelimited.asSubroutine 37 53 ++ [.halt]) 29
    (by change 0 < 6; decide) rfl tupleHalt skipUnary_control_closed
  change RunsFor copyStoredMiddleElement (frameFinish.resumeAt 22) (tupleFinish.resumeAt 29) c at hTuple
  have toFirst := toTuple.trans hTuple
  obtain ⟨firstFinish, d, hd, firstRun, firstHalt, firstOutput⟩ :=
    skipDelimited_terminates_from_anyTape tupleFinish.inputTape tupleFinish.outputTape
  have hFirst := firstRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29) skipDelimited
    (copyDelimited.asSubroutine 37 53 ++ [.halt]) 37
    (by change 0 < 7; decide) rfl firstHalt skipDelimited_control_closed
  change RunsFor copyStoredMiddleElement (tupleFinish.resumeAt 29) (firstFinish.resumeAt 37) d at hFirst
  have toSecond := toFirst.trans hFirst

  obtain ⟨copied, e, he, copyRun, copyHalt⟩ :=
    copyDelimited_terminates_from_anyTape firstFinish.inputTape firstFinish.outputTape
  have hCopy := copyRun.withSubroutine_halted_of_closed
    (skipUnary.asSubroutine 0 7 ++ [.moveRight .output] ++ skipFrame.asSubroutine 8 22 ++
      skipUnary.asSubroutine 22 29 ++ skipDelimited.asSubroutine 29 37) copyDelimited [.halt] 53
    (by change 0 < 15; decide) rfl copyHalt copyDelimited_control_closed
  change RunsFor copyStoredMiddleElement (firstFinish.resumeAt 37) (copied.resumeAt 53) e at hCopy
  let finish : Configuration := { copied with pc := 53, halted := true }
  have last : Step copyStoredMiddleElement (copied.resumeAt 53) finish := by
    have code : copyStoredMiddleElement[53]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, a + 1 + b + c + d + e + 1, ?_, RunsFor.succ (toSecond.trans hCopy) last, rfl, ?_, ?_⟩
  · have frameStorage := GuardedCompiler.sourceStorage_le_of_run toFrame
    change frameStart.inputTape.cells + frameStart.outputTape.cells ≤ input.cells + output.cells + (a + 1) at frameStorage
    have tupleStorage := GuardedCompiler.sourceStorage_le_of_run toTuple
    change frameFinish.inputTape.cells + frameFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b) at tupleStorage
    have firstStorage := GuardedCompiler.sourceStorage_le_of_run toFirst
    change tupleFinish.inputTape.cells + tupleFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b + c) at firstStorage
    have copyStorage := GuardedCompiler.sourceStorage_le_of_run toSecond
    change firstFinish.inputTape.cells + firstFinish.outputTape.cells ≤ input.cells + output.cells + (a + 1 + b + c + d) at copyStorage
    omega
  · obtain ⟨publicCount, publicRight⟩ := skipUnary_input_right_suffix publicRun
    obtain ⟨frameCount, frameRight⟩ := skipFrame_input_right_suffix frameRun
    obtain ⟨tupleCount, tupleRight⟩ := skipUnary_input_right_suffix tupleRun
    obtain ⟨firstCount, firstRight⟩ := skipDelimited_input_right_suffix firstRun
    obtain ⟨copyCount, copyRight⟩ := copyDelimited_input_right_suffix copyRun
    change publicFinish.inputTape.right = input.right.drop publicCount at publicRight
    change frameFinish.inputTape.right = publicFinish.inputTape.right.drop frameCount at frameRight
    change tupleFinish.inputTape.right = frameFinish.inputTape.right.drop tupleCount at tupleRight
    change firstFinish.inputTape.right = tupleFinish.inputTape.right.drop firstCount at firstRight
    change copied.inputTape.right = firstFinish.inputTape.right.drop copyCount at copyRight
    refine ⟨publicCount + frameCount + tupleCount + firstCount + copyCount, ?_⟩
    change copied.inputTape.right = _
    simp only [copyRight, firstRight, tupleRight, frameRight, publicRight, List.drop_drop]
  · intro before blanks hOutput
    have hFrameEntry : frameStart.outputTape =
        ({ left := none :: before, right := List.replicate (blanks - 1) none } : Tape) := by
      cases blanks <;> simp [frameStart, publicOutput, hOutput, Tape.moveRight, List.replicate_succ]
    obtain ⟨freshFrame, freshFrameTime, frameSaved, frameBlanks,
      _hFreshFrameTime, freshFrameRun, freshFrameHalt, freshFrameOutput⟩ :=
      skipFrameCells_terminates_with_layout frameStart.inputTape before (blanks - 1)
    rw [hFrameEntry] at frameRun
    have hFrameSame := frameRun.halted_finish_eq_of_no_randomBit freshFrameRun frameHalt freshFrameHalt skipFrame_no_randomBit
    have hFrameOutput : frameFinish.outputTape =
        ({ left := frameSaved, right := List.replicate frameBlanks none } : Tape) := by
      rw [hFrameSame]
      exact freshFrameOutput
    have hCopyEntry := firstOutput.trans (tupleOutput.trans hFrameOutput)
    obtain ⟨freshCopy, freshCopyTime, after, remaining,
      _hFreshCopyTime, freshCopyRun, freshCopyHalt, freshCopyOutput⟩ :=
      copyDelimited_terminates_with_output_layout firstFinish.inputTape frameSaved frameBlanks
    rw [hCopyEntry] at copyRun
    have hCopySame := copyRun.halted_finish_eq_of_no_randomBit freshCopyRun copyHalt freshCopyHalt copyDelimited_no_randomBit
    refine ⟨after, remaining, ?_⟩
    change copied.outputTape = _
    rw [hCopySame]
    exact freshCopyOutput

theorem copyStoredMiddleElement_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor copyStoredMiddleElement
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hSuffix, _hLayout⟩ := copyStoredMiddleElement_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Public-prefix scanning and escaped-field copying retain a fresh output
frontier on arbitrary finite input tapes. This also covers a missing payload
bit or an invalid frame header; the returned field may then be a partial copy. -/
theorem copyStoredMiddleElement_terminates_with_suffix_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000 ∧
      RunsFor copyStoredMiddleElement
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } ∧
      ∃ count, finish.inputTape.right = input.right.drop count := by
  obtain ⟨finish, used, hBound, run, hHalted, hSuffix, hLayout⟩ :=
    copyStoredMiddleElement_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput, hSuffix⟩

/-- Output-frontier specialization of the stronger retained-input theorem.
The same actual trace supplies both stopping and fresh scratch. -/
theorem copyStoredMiddleElement_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000 ∧
      RunsFor copyStoredMiddleElement
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput, _hSuffix⟩ :=
    copyStoredMiddleElement_terminates_with_suffix_layout input before blanks
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩

theorem copyStoredMiddleElement_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor copyStoredMiddleElement
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000 * (input.cells + output.cells) + 1000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := copyStoredMiddleElement_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted copyStoredMiddleElement_no_randomBit hBound finish trace

end Machine
