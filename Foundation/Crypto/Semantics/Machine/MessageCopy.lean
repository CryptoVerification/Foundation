import Foundation.Crypto.Semantics.Machine.MessageSelection
import Foundation.Crypto.Semantics.Machine.DelimitedInput

namespace Machine

/-- Copy the selected canonical field with the existing native parser, then
remove its status bit by two charged tape instructions. The copied message
ends at a blank cell and the caller's saved challenge remains untouched. -/
def copyMessageField : Program :=
  readDelimited.asSubroutine 0 17 ++ [.moveLeft .output, .erase .output, .halt]

def copyMessageFieldFinish (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) : Configuration :=
  { readDelimitedContextFinish beforeInput beforeOutput field tail with
    pc := 19, outputTape := { left := field.reverse.map some ++ beforeOutput, right := [none] } }

/-- Every copied bit uses the existing seven/eight-step parser loop.
Returning replaces its halt with a jump. Moving onto and erasing the status
cell and the final caller halt cost three further transitions. -/
theorem copyMessageField_runs (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    RunsFor copyMessageField (readDelimitedContextStart beforeInput beforeOutput field tail)
      (copyMessageFieldFinish beforeInput beforeOutput field tail)
      (readDelimitedSteps (FiniteBitEncoding.delimit field) + 3) := by
  have hRead := (readDelimitedContext_runs beforeInput beforeOutput field tail).withSubroutine_halted_of_closed
    [] readDelimited [.moveLeft .output, .erase .output, .halt] 17
    (by change 0 < 16; decide) rfl rfl readDelimited_control_closed
  change RunsFor copyMessageField (readDelimitedContextStart beforeInput beforeOutput field tail)
    ((readDelimitedContextFinish beforeInput beforeOutput field tail).resumeAt 17)
    (readDelimitedSteps (FiniteBitEncoding.delimit field)) at hRead
  let returned := (readDelimitedContextFinish beforeInput beforeOutput field tail).resumeAt 17
  let moved : Configuration := { returned with pc := 18, outputTape := returned.outputTape.moveLeft }
  let erased : Configuration := { moved with pc := 19, outputTape := moved.outputTape.write none }
  have h0 : Step copyMessageField returned moved := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, returned, moved, readDelimitedContextFinish, Configuration.resumeAt,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step copyMessageField moved erased := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, returned, moved, erased, readDelimitedContextFinish,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step copyMessageField erased (copyMessageFieldFinish beforeInput beforeOutput field tail) := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, returned, moved, erased, readDelimitedContextFinish,
      copyMessageFieldFinish, Configuration.resumeAt, Instruction.next, Tape.moveLeft, Tape.write]
  simpa only [Nat.add_assoc] using RunsFor.succ (RunsFor.succ (RunsFor.succ hRead h0) h1) h2

theorem copyMessageField_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyMessageField := by
  simp [copyMessageField, readDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem copyMessageField_eval (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    evalConfigWithin copyMessageField (readDelimitedContextStart beforeInput beforeOutput field tail)
      (readDelimitedSteps (FiniteBitEncoding.delimit field) + 3) =
      PMF.pure (copyMessageFieldFinish beforeInput beforeOutput field tail) :=
  (copyMessageField_runs beforeInput beforeOutput field tail).evalConfigWithin_eq_pure_of_no_randomBit
    copyMessageField_no_randomBit

/-- Resume copying from the actual configuration returned by message
selection. Both cases use the selected field's existing cells. The challenge
bit and its blank separator are retained in the same saved output prefix. -/
theorem selectMessageFinish_copy_layout (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) :
    (selectMessageFinish beforeInput beforeOutput first second stateTail bit).resumeAt 0 =
      readDelimitedContextStart
        (if bit then (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: beforeInput
          else some false :: beforeInput)
        (none :: some bit :: beforeOutput)
        (if bit then second else first)
        (if bit then stateTail else (FiniteBitEncoding.delimit second).map some ++ stateTail) := by
  change ({
      pc := 0
      inputTape := (selectMessageFinish beforeInput beforeOutput first second stateTail bit).inputTape,
      outputTape := (selectMessageFinish beforeInput beforeOutput first second stateTail bit).outputTape,
      halted := false } : Configuration) = _
  rw [selectMessageFinish_input, selectMessageFinish_output,
    readDelimitedContextStart_layout, skipDelimitedStart_layout]

/-- The output tape contains the selected raw element code followed by a
blank at the head. The saved native challenge bit lies behind a second blank;
no parser success bit is leaked into a later group-operation argument. -/
theorem copyMessageFieldFinish_output (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    (copyMessageFieldFinish beforeInput beforeOutput field tail).outputTape =
      { left := field.reverse.map some ++ beforeOutput, right := [none] } := rfl

theorem copyMessageField_steps_le (field : List Bool) :
    readDelimitedSteps (FiniteBitEncoding.delimit field) + 3 ≤ 8 * field.length + 12 := by
  have h := readDelimitedSteps_le (FiniteBitEncoding.delimit field)
  rw [FiniteBitEncoding.delimit_length] at h
  omega

theorem copyMessageField_control_closed (c d : Configuration)
    (hPc : c.pc < copyMessageField.length) (step : Step copyMessageField c d)
    (_hRunning : d.halted = false) : d.pc < copyMessageField.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 20 at hPc
  change d.pc < 20
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, copyMessageField,
    readDelimited, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem copyMessageField_from_parser (input output : Tape) (parsed : Configuration)
    (parseTime : Nat)
    (hRun : RunsFor readDelimited
      ({ inputTape := input, outputTape := output } : Configuration) parsed parseTime)
    (hHalt : parsed.halted = true) :
    RunsFor copyMessageField
      ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 19, inputTape := parsed.inputTape,
         outputTape := parsed.outputTape.moveLeft.write none, halted := true } : Configuration)
      (parseTime + 3) := by
  have hParse := hRun.withSubroutine_halted_of_closed
    [] readDelimited [.moveLeft .output, .erase .output, .halt] 17
    (by change 0 < 16; decide) rfl hHalt readDelimited_control_closed
  change RunsFor copyMessageField ({ inputTape := input, outputTape := output } : Configuration)
    (parsed.resumeAt 17) parseTime at hParse
  let moved : Configuration := { pc := 18, inputTape := parsed.inputTape, outputTape := parsed.outputTape.moveLeft }
  let erased : Configuration := { moved with pc := 19, outputTape := moved.outputTape.write none }
  have hMove : Step copyMessageField (parsed.resumeAt 17) moved := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hErase : Step copyMessageField moved erased := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, moved, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hStop : Step copyMessageField erased { erased with halted := true } := by
    simp [Step, successors, next, copyMessageField, readDelimited, Program.asSubroutine,
      Instruction.asSubroutine, erased, Instruction.next]
  simpa only [Nat.add_assoc] using RunsFor.succ (RunsFor.succ (RunsFor.succ hParse hMove) hErase) hStop

/-- The selected-field copier also stops on malformed fields and dirty
finite tapes. The native parser's status cell is erased by two charged
instructions; this theorem does not claim successful field decoding. -/
theorem copyMessageField_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 8 * input.cells + 9 ∧
      RunsFor copyMessageField ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨parsed, parseTime, hTime, hRun, hHalt⟩ := readDelimited_terminates_from_anyTape input output
  exact ⟨_, parseTime + 3, by omega, copyMessageField_from_parser input output parsed parseTime hRun hHalt, rfl⟩

/-- Status erasure returns to a fresh output frontier even on malformed
input. The saved caller prefix is retained in the finite physical tape;
this layout property asserts no successful decoding of the copied bits. -/
theorem copyMessageField_terminates_with_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 8 * input.cells + 9 ∧
      RunsFor copyMessageField
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨parsed, parseTime, after, remaining, hTime, hRun, hHalt, hOutput⟩ :=
    readDelimited_terminates_with_output_layout input savedOutput blanks
  refine ⟨_, parseTime + 3, after.tail, remaining + 1, by omega,
    copyMessageField_from_parser input _ parsed parseTime hRun hHalt, rfl, ?_⟩
  cases after <;> simp [hOutput, Tape.moveLeft, Tape.write, List.replicate_succ]

theorem copyMessageField_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor copyMessageField
      ({ inputTape := input, outputTape := output } : Configuration) finish (8 * input.cells + 9)) :
    finish.halted = true := by
  obtain ⟨target, used, hBound, hRun, hHalt⟩ := copyMessageField_terminates_from_anyTape input output
  have hEval := hRun.evalConfigWithin_eq_pure_of_no_randomBit copyMessageField_no_randomBit
  have hAll (c : Configuration)
      (trace : PaddedRunsFor copyMessageField
        ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hEval] at hMem
    have hEq : c = target := by simpa using hMem
    simpa only [hEq] using hHalt
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAll, hEval] at hMem
  have hEq : finish = target := by simpa using hMem
  simpa only [hEq] using hHalt

/-- Common-budget stopping and fresh-frontier certificate for all finite
input tapes. Failure status is erased by actual instructions before return. -/
theorem copyMessageField_haltsFrom_with_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor copyMessageField
      ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
      finish (8 * input.cells + 9)) :
    finish.halted = true ∧
      ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨target, used, after, remaining, hBound, trace, hHalt, hOutput⟩ :=
    copyMessageField_terminates_with_output_layout input savedOutput blanks
  have hEval := trace.evalConfigWithin_eq_pure_of_no_randomBit copyMessageField_no_randomBit
  have hAt (c : Configuration) (hc : PaddedRunsFor copyMessageField
      ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
      c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval, PMF.mem_support_pure_iff] at hMem
    simpa only [hMem] using hHalt
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hEval, PMF.mem_support_pure_iff] at hMem
  subst finish
  exact ⟨hHalt, after, remaining, hOutput⟩

private theorem copyMessageField_step_input_moveRight (c d : Configuration) (step : Step copyMessageField c d) :
    d.inputTape = c.inputTape ∨ d.inputTape = c.inputTape.moveRight := by
  have hActive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) step)
  by_cases hPc : c.pc < 20
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, copyMessageField,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : copyMessageField[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 20 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

/-- Parsing and status cleanup preserve every input cell and only move
the input head right, even when the selected field is malformed. -/
theorem copyMessageField_input_moveRight {start finish : Configuration} {used : Nat}
    (run : PaddedRunsFor copyMessageField start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape := by
  obtain ⟨actualTime, hTime, actual⟩ := run.toRunsFor_le
  obtain ⟨moves, hMoves, hInput⟩ := actual.input_moveRight_of_step copyMessageField_step_input_moveRight
  exact ⟨moves, hMoves.trans hTime, hInput⟩


end Machine
