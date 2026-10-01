import Foundation.Machine.ContextualFrame
import Foundation.Machine.GuardedTrace

namespace Machine

/-- Frame a raw payload preceded by a known false delimiter. Temporarily
blank that one delimiter so the existing rewind routine stops there, then
restore it by an actual write. No stored prefix cell is discarded. -/
def writeFrameAfterFalse : Program :=
  [.moveLeft .input, .erase .input, .moveRight .input] ++ writeFrame.asSubroutine 3 28 ++
  rewindBitstring.asSubroutine 28 33 ++ [.moveLeft .input, .write .input false, .moveRight .input, .halt]

private def afterDelimiterTape (savedInput tail : List (Option Bool)) (bits : List Bool) : Tape :=
  { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
    left := some false :: savedInput }

def writeFrameAfterFalseStart (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := afterDelimiterTape savedInput tail bits,
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def writeFrameAfterFalseFinish (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 36, inputTape := afterDelimiterTape savedInput tail bits,
    outputTape := {
      left := (frame bits).reverse.map some ++ beforeOutput
      right := List.replicate (blanks - (2 * bits.length + 1)) none },
    halted := true }

def writeFrameAfterFalseSteps (bits : List Bool) : Nat :=
  3 + writeFrameSteps bits + (2 * bits.length + 4) + 4

set_option maxHeartbeats 600000 in
theorem writeFrameAfterFalse_runs (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor writeFrameAfterFalse (writeFrameAfterFalseStart savedInput beforeOutput tail bits blanks)
      (writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks) (writeFrameAfterFalseSteps bits) := by
  let start := writeFrameAfterFalseStart savedInput beforeOutput tail bits blanks
  let delimiter : Configuration :=
    { pc := 1, inputTape := {
        left := savedInput
        current := some false
        right := bits.map some ++ none :: tail }, outputTape := start.outputTape }
  let erased : Configuration :=
    { delimiter with pc := 2, inputTape := delimiter.inputTape.write none }
  let frameStart := writeFrameContextPaddedStart savedInput beforeOutput tail bits blanks
  have hLeft : Step writeFrameAfterFalse start delimiter := by
    cases bits <;> simp [Step, successors, next, writeFrameAfterFalse, start,
      writeFrameAfterFalseStart, afterDelimiterTape, delimiter, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveLeft, Tape.moveRight]
  have hErase : Step writeFrameAfterFalse delimiter erased := by
    simp [Step, successors, next, writeFrameAfterFalse, delimiter, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.write]
  have hRight : Step writeFrameAfterFalse erased (frameStart.rebasePc 3) := by
    cases bits <;> simp [Step, successors, next, writeFrameAfterFalse, erased, delimiter,
      start, writeFrameAfterFalseStart, frameStart, writeFrameContextPaddedStart_layout,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Configuration.rebasePc, Tape.moveRight, Tape.write]
  have hFrame := (writeFrameContextPadded_runs savedInput beforeOutput tail bits blanks).withSubroutine_halted_of_closed
    [.moveLeft .input, .erase .input, .moveRight .input] writeFrame
    (rewindBitstring.asSubroutine 28 33 ++ [.moveLeft .input, .write .input false, .moveRight .input, .halt]) 28
    (by change 0 < 24; decide) rfl rfl writeFrame_control_closed
  let framed := writeFrameContextPaddedFinish savedInput beforeOutput tail bits blanks
  change RunsFor writeFrameAfterFalse (frameStart.rebasePc 3) (framed.resumeAt 28)
    (writeFrameSteps bits) at hFrame
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := savedInput, right := bits.map some ++ none :: tail } : Tape).moveRight,
      outputTape := framed.outputTape, halted := true }
  have hRewind := (rewindScratch_runs_from savedInput bits none tail framed.outputTape).withSubroutine_halted_of_closed
    ([.moveLeft .input, .erase .input, .moveRight .input] ++ writeFrame.asSubroutine 3 28)
    rewindBitstring [.moveLeft .input, .write .input false, .moveRight .input, .halt] 33
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor writeFrameAfterFalse (framed.resumeAt 28) (rewound.resumeAt 33)
    (2 * bits.length + 4) at hRewind
  let blank : Configuration :=
    { pc := 34, inputTape := { left := savedInput, right := bits.map some ++ none :: tail },
      outputTape := framed.outputTape }
  let restored : Configuration :=
    { blank with pc := 35, inputTape := blank.inputTape.write (some false) }
  have hBack : Step writeFrameAfterFalse (rewound.resumeAt 33) blank := by
    cases bits <;> simp [Step, successors, next, writeFrameAfterFalse, writeFrame,
      writeFrameHeader, copyBitstring, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, rewound, blank, Configuration.resumeAt,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.moveLeft]
  have hRestore : Step writeFrameAfterFalse blank restored := by
    simp [Step, successors, next, writeFrameAfterFalse, writeFrame,
      writeFrameHeader, copyBitstring, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, blank, restored, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.write]
  have hForward : Step writeFrameAfterFalse restored
      ((writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks).resumeAt 36) := by
    cases bits <;> simp [Step, successors, next, writeFrameAfterFalse, writeFrame,
      writeFrameHeader, copyBitstring, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, blank, restored, framed, writeFrameContextPaddedFinish,
      writeFrameAfterFalseFinish, afterDelimiterTape, Configuration.resumeAt,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
  have hHalt : Step writeFrameAfterFalse
      ((writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks).resumeAt 36)
      (writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks) := by
    simp [Step, successors, next, writeFrameAfterFalse, writeFrame,
      writeFrameHeader, copyBitstring, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, writeFrameAfterFalseFinish, Configuration.resumeAt, Instruction.next]
  have beforeFrame := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hLeft) hErase) hRight
  have run := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    ((beforeFrame.trans hFrame).trans hRewind) hBack) hRestore) hForward) hHalt
  simpa only [writeFrameAfterFalseSteps] using run

theorem writeFrameAfterFalse_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ writeFrameAfterFalse := by
  simp [writeFrameAfterFalse, writeFrame, writeFrameHeader, copyBitstring,
    rewindBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem writeFrameAfterFalse_eval (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin writeFrameAfterFalse
      (writeFrameAfterFalseStart savedInput beforeOutput tail bits blanks)
      (writeFrameAfterFalseSteps bits) =
      PMF.pure (writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks) :=
  (writeFrameAfterFalse_runs savedInput beforeOutput tail bits blanks).evalConfigWithin_eq_pure_of_no_randomBit
    writeFrameAfterFalse_no_randomBit

theorem writeFrameAfterFalse_steps_le (bits : List Bool) :
    writeFrameAfterFalseSteps bits ≤ 15 * bits.length + 22 := by
  have h := writeFrameSteps_le bits
  simp only [writeFrameAfterFalseSteps]
  omega

theorem writeFrameAfterFalseStart_layout (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    writeFrameAfterFalseStart savedInput beforeOutput tail bits blanks =
      { inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
          left := some false :: savedInput },
        outputTape := { left := beforeOutput, right := List.replicate blanks none } } := rfl

theorem writeFrameAfterFalseFinish_input (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    (writeFrameAfterFalseFinish savedInput beforeOutput tail bits blanks).inputTape =
      { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
          left := some false :: savedInput } := rfl

set_option maxHeartbeats 600000 in
theorem writeFrameAfterFalse_control_closed (c d : Configuration)
    (hPc : c.pc < writeFrameAfterFalse.length) (step : Step writeFrameAfterFalse c d)
    (_hRunning : d.halted = false) : d.pc < writeFrameAfterFalse.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 37 at hPc
  change d.pc < 37
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, writeFrameAfterFalse,
    writeFrame, writeFrameHeader, rewindBitstring, copyBitstring, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


/-- Temporarily editing the presumed delimiter is also safe for stopping on
arbitrary finite tapes. Malformed data need not be serialized correctly;
the actual frame and rewind subroutines still have finite linear cost. -/
theorem writeFrameAfterFalse_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 100000 * (input.cells + output.cells) + 100000 ∧
      RunsFor writeFrameAfterFalse
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  let moved : Configuration := { pc := 1, inputTape := input.moveLeft, outputTape := output }
  let erased : Configuration := { moved with pc := 2, inputTape := moved.inputTape.write none }
  let frameStart : Configuration := { erased with pc := 3, inputTape := erased.inputTape.moveRight }
  have a : Step writeFrameAfterFalse ({ inputTape := input, outputTape := output } : Configuration) moved := by
    have code : writeFrameAfterFalse[0]? = some (.moveLeft .input) := rfl
    simp [Step, successors, next, code, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have b : Step writeFrameAfterFalse moved erased := by
    have code : writeFrameAfterFalse[1]? = some (.erase .input) := rfl
    simp [Step, successors, next, code, moved, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step writeFrameAfterFalse erased frameStart := by
    have code : writeFrameAfterFalse[2]? = some (.moveRight .input) := rfl
    simp [Step, successors, next, code, moved, erased, frameStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have toFrame := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c
  obtain ⟨framed, frameTime, hFrameTime, frameRun, frameHalt⟩ :=
    writeFrame_terminates_from_anyTape frameStart.inputTape frameStart.outputTape
  have hFrame := frameRun.withSubroutine_halted_of_closed
    [.moveLeft .input, .erase .input, .moveRight .input] writeFrame
    (rewindBitstring.asSubroutine 28 33 ++ [.moveLeft .input, .write .input false, .moveRight .input, .halt]) 28
    (by change 0 < 24; decide) rfl frameHalt writeFrame_control_closed
  change RunsFor writeFrameAfterFalse frameStart (framed.resumeAt 28) frameTime at hFrame
  have toRewind := toFrame.trans hFrame
  obtain ⟨rewound, rewindTime, hRewindTime, rewindRun, rewindHalt, _rewindOutput⟩ :=
    rewindBitstring_terminates_from framed.inputTape framed.outputTape
  have hRewind := rewindRun.withSubroutine_halted_of_closed
    ([.moveLeft .input, .erase .input, .moveRight .input] ++ writeFrame.asSubroutine 3 28)
    rewindBitstring [.moveLeft .input, .write .input false, .moveRight .input, .halt] 33
    (by change 0 < 4; decide) rfl rewindHalt rewindBitstring_control_closed
  change RunsFor writeFrameAfterFalse (framed.resumeAt 28) (rewound.resumeAt 33) rewindTime at hRewind
  let back : Configuration := { pc := 34, inputTape := rewound.inputTape.moveLeft, outputTape := rewound.outputTape }
  let restored : Configuration := { back with pc := 35, inputTape := back.inputTape.write (some false) }
  let forward : Configuration := { restored with pc := 36, inputTape := restored.inputTape.moveRight }
  let finish : Configuration := { forward with halted := true }
  have d : Step writeFrameAfterFalse (rewound.resumeAt 33) back := by
    have code : writeFrameAfterFalse[33]? = some (.moveLeft .input) := rfl
    simp [Step, successors, next, code, back, Configuration.resumeAt, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have e : Step writeFrameAfterFalse back restored := by
    have code : writeFrameAfterFalse[34]? = some (.write .input false) := rfl
    simp [Step, successors, next, code, back, restored, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have f : Step writeFrameAfterFalse restored forward := by
    have code : writeFrameAfterFalse[35]? = some (.moveRight .input) := rfl
    simp [Step, successors, next, code, restored, forward, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have g : Step writeFrameAfterFalse forward finish := by
    have code : writeFrameAfterFalse[36]? = some .halt := rfl
    simp [Step, successors, next, code, forward, finish, Instruction.next]
  refine ⟨finish, 3 + frameTime + rewindTime + 4, ?_, ?_, rfl⟩
  · have firstStorage := GuardedCompiler.sourceStorage_le_of_run toFrame
    change frameStart.inputTape.cells + frameStart.outputTape.cells ≤ input.cells + output.cells + 3 at firstStorage
    have frameStorage := GuardedCompiler.sourceStorage_le_of_run toRewind
    change framed.inputTape.cells + framed.outputTape.cells ≤ input.cells + output.cells + (3 + frameTime) at frameStorage
    have hLeft : framed.inputTape.left.length ≤ framed.inputTape.cells := by
      dsimp only [Tape.cells]; omega
    omega
  · exact RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.succ (toRewind.trans hRewind) d) e) f) g

end Machine
