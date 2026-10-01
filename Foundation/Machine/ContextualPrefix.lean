import Foundation.Machine.ContextualInput
import Foundation.Machine.ProtocolPrefix

namespace Machine

/-- Contextual invocation of the existing public-prefix copying code.
A real blank separates the copied input prefix from earlier caller data.
Following cells can include a saved DDH tuple and an arbitrary source reply. -/
def savePublicPrefixContextStart (savedInput beforeOutput : List (Option Bool))
    (publicBits : List Bool) (tail : List (Option Bool)) (blanks : Nat) : Configuration :=
  { inputTape := {
      left := publicBits.reverse.map some ++ none :: savedInput
      current := some true
      right := tail },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def savePublicPrefixContextFinish (savedInput beforeOutput : List (Option Bool))
    (publicBits : List Bool) (tail : List (Option Bool)) (blanks : Nat) : Configuration :=
  { pc := 16,
    inputTape := {
      left := publicBits.reverse.map some ++ none :: savedInput
      current := some true
      right := tail },
    outputTape := {
      left := publicBits.reverse.map some ++ beforeOutput
      right := List.replicate (blanks - publicBits.length) none },
    halted := true }

/-- Every temporary erasure, head rewind, copied bit and restoring write is
performed by the same seventeen native instructions. Protected data on
both tapes remain in the full configuration, not only in its observation. -/
theorem savePublicPrefixContext_runs (savedInput beforeOutput : List (Option Bool))
    (publicBits : List Bool) (tail : List (Option Bool)) (blanks : Nat) :
    RunsFor savePublicPrefix (savePublicPrefixContextStart savedInput beforeOutput publicBits tail blanks)
      (savePublicPrefixContextFinish savedInput beforeOutput publicBits tail blanks)
      (savePublicPrefixSteps publicBits) := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let erased : Configuration :=
    { pc := 1, inputTape := { left := publicBits.reverse.map some ++ none :: savedInput, right := tail },
      outputTape := output }
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := savedInput, right := publicBits.map some ++ none :: tail } : Tape).moveRight,
      outputTape := output, halted := true }
  have hErase : Step savePublicPrefix (savePublicPrefixContextStart savedInput beforeOutput publicBits tail blanks) erased := by
    simp [Step, successors, next, savePublicPrefix, savePublicPrefixContextStart, erased, output,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write]
  have hRewind := (rewindScratch_runs_from savedInput publicBits none tail output).withSubroutine_halted_of_closed
    [.erase .input] rewindBitstring (copyBitstring.asSubroutine 6 15 ++ [.write .input true, .halt]) 6
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor savePublicPrefix erased (rewound.resumeAt 6) (2 * publicBits.length + 4) at hRewind
  have hCopyStart : rewound.resumeAt 6 =
      (copySegmentStart (none :: savedInput) beforeOutput tail publicBits blanks).rebasePc 6 := by
    cases publicBits <;> simp [rewound, copySegmentStart_layout, Configuration.resumeAt,
      Configuration.rebasePc, output, Tape.moveRight]
  rw [hCopyStart] at hRewind
  have hCopy := (copySegment_runs (none :: savedInput) beforeOutput tail publicBits blanks).withSubroutine_halted_of_closed
    ([.erase .input] ++ rewindBitstring.asSubroutine 1 6) copyBitstring [.write .input true, .halt] 15
    (by change 0 < 8; decide) rfl rfl GuardedCompiler.copyBitstring_control_closed
  change RunsFor savePublicPrefix
    ((copySegmentStart (none :: savedInput) beforeOutput tail publicBits blanks).rebasePc 6)
    ((copySegmentFinish (none :: savedInput) beforeOutput tail publicBits blanks).resumeAt 15)
    (copyBitstringSteps publicBits) at hCopy
  let written : Configuration :=
    { savePublicPrefixContextFinish savedInput beforeOutput publicBits tail blanks with halted := false }
  have hWrite : Step savePublicPrefix
      ((copySegmentFinish (none :: savedInput) beforeOutput tail publicBits blanks).resumeAt 15) written := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, copySegmentFinish, Configuration.resumeAt,
      written, savePublicPrefixContextFinish, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.write]
  have hHalt : Step savePublicPrefix written
      (savePublicPrefixContextFinish savedInput beforeOutput publicBits tail blanks) := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, written, savePublicPrefixContextFinish, Instruction.next]
  simpa only [savePublicPrefixSteps, Nat.add_assoc, Nat.zero_add, Nat.reduceAdd] using
    RunsFor.succ (RunsFor.succ (((RunsFor.succ (RunsFor.zero _) hErase).trans hRewind).trans hCopy)
      hWrite) hHalt

/-- Native public-input assembly in a caller which already holds source
scratch data on its output tape. Two charged output moves reserve a blank
before the new input. The frame scanner's counter never touches saved data. -/
def preparePublicPrefixContext : Program :=
  [.moveRight .output] ++ skipUnary.asSubroutine 1 8 ++ skipFrame.asSubroutine 8 22 ++
    [.moveRight .output] ++ savePublicPrefix.asSubroutine 23 41 ++ [.halt]

def preparePublicPrefixContextStart (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) : Configuration :=
  skipUnaryCellsStart (none :: savedInput) n
    ((frame instanceBits).map some ++ some true :: tail) { left := savedOutput }

def preparePublicPrefixContextFinish (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) : Configuration :=
  { savePublicPrefixContextFinish savedInput (none :: savedOutput)
      (encodeSecurityParameter n ++ frame instanceBits) tail instanceBits.length with pc := 41 }

def preparePublicPrefixContextSteps (n : Nat) (instanceBits : List Bool) : Nat :=
  1 + (3 * n + 3) + (10 * instanceBits.length + 5) + 1 +
    savePublicPrefixSteps (encodeSecurityParameter n ++ frame instanceBits) + 1

/-- Copy the public input after caller data while retaining explicit blank
padding from an earlier native stage. If the padding fits within the instance
counter, prefix copying consumes it; no finite tape cells are discarded. -/
def preparePublicPrefixContextPaddedStart (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) (blanks : Nat) : Configuration :=
  skipUnaryCellsStart (none :: savedInput) n
    ((frame instanceBits).map some ++ some true :: tail)
    { left := savedOutput, right := List.replicate blanks none }

theorem preparePublicPrefixContextPadded_runs (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool))
    (blanks : Nat) (hBlanks : blanks ≤ instanceBits.length + 1) :
    RunsFor preparePublicPrefixContext
      (preparePublicPrefixContextPaddedStart savedInput savedOutput n instanceBits tail blanks)
      (preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail)
      (preparePublicPrefixContextSteps n instanceBits) := by
  let a := skipUnary.asSubroutine 1 8
  let b := skipFrame.asSubroutine 8 22
  let k := savePublicPrefix.asSubroutine 23 41
  let before := some false :: (List.replicate n (some true) ++ none :: savedInput)
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let output : Tape := { left := none :: savedOutput, right := List.replicate (blanks - 1) none }
  have hMove : Step preparePublicPrefixContext
      (preparePublicPrefixContextPaddedStart savedInput savedOutput n instanceBits tail blanks)
      ((skipUnaryCellsStart (none :: savedInput) n
        ((frame instanceBits).map some ++ some true :: tail) output).rebasePc 1) := by
    cases blanks <;> simp [Step, successors, next, preparePublicPrefixContext, preparePublicPrefixContextPaddedStart,
      skipUnaryCellsStart_layout, Configuration.rebasePc, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveRight, output, List.replicate_succ]
  have hUnary := (skipUnaryCells_runs (none :: savedInput) n
      ((frame instanceBits).map some ++ some true :: tail) output).withSubroutine_halted_of_closed
    [.moveRight .output] skipUnary (b ++ [.moveRight .output] ++ k ++ [.halt]) 8
    (by simp [skipUnaryCellsStart_layout, skipUnary]) rfl rfl skipUnary_control_closed
  change RunsFor preparePublicPrefixContext
    ((skipUnaryCellsStart (none :: savedInput) n
      ((frame instanceBits).map some ++ some true :: tail) output).rebasePc 1)
    ((skipUnaryCellsFinish (none :: savedInput) n
      ((frame instanceBits).map some ++ some true :: tail) output).resumeAt 8)
    (3 * n + 3) at hUnary
  have hFrameStart : (skipUnaryCellsFinish (none :: savedInput) n
      ((frame instanceBits).map some ++ some true :: tail) output).resumeAt 8 =
      (skipFrameCellsPaddedStart before savedOutput instanceBits.length
        (instanceBits.map some ++ some true :: tail) (blanks - 1)).rebasePc 8 := by
    cases instanceBits <;> simp [skipUnaryCellsFinish_layout, skipFrameCellsPaddedStart_layout,
      Configuration.resumeAt, Configuration.rebasePc, before, frame, List.map_append,
      Tape.moveRight, List.replicate_succ, output]
  rw [hFrameStart] at hUnary
  have hFrame := (skipFrameCellsPadded_runs before savedOutput instanceBits.length
      (instanceBits.map some ++ some true :: tail) (blanks - 1)).withSubroutine_halted_of_closed
    ([.moveRight .output] ++ a) skipFrame ([.moveRight .output] ++ k ++ [.halt]) 22
    (by simp [skipFrameCellsPaddedStart_layout, skipFrame]) rfl rfl skipFrame_control_closed
  change RunsFor preparePublicPrefixContext
    ((skipFrameCellsPaddedStart before savedOutput instanceBits.length
      (instanceBits.map some ++ some true :: tail) (blanks - 1)).rebasePc 8)
    ((skipFrameCellsPaddedFinish before savedOutput instanceBits.length
      (instanceBits.map some ++ some true :: tail) (blanks - 1)).resumeAt 22)
    (10 * instanceBits.length + 5) at hFrame
  have hOutput : (skipFrameCellsPaddedFinish before savedOutput instanceBits.length
      (instanceBits.map some ++ some true :: tail) (blanks - 1)).outputTape =
      ({ left := savedOutput, right := List.replicate (instanceBits.length + 1) none } : Tape) := by
    have hPad : blanks - 1 - instanceBits.length = 0 := by omega
    simp [skipFrameCellsPaddedFinish, hPad]
  have hInput : (skipFrameCellsPaddedFinish before savedOutput instanceBits.length
      (instanceBits.map some ++ some true :: tail) (blanks - 1)).inputTape =
      { left := instanceBits.reverse.map some ++ some false ::
          (List.replicate instanceBits.length (some true) ++ before)
        current := some true
        right := tail } :=
    skipFrameCellsFinish_input before savedOutput instanceBits (some true) tail
  have hAfter : Step preparePublicPrefixContext
      ((skipFrameCellsPaddedFinish before savedOutput instanceBits.length
        (instanceBits.map some ++ some true :: tail) (blanks - 1)).resumeAt 22)
      ((savePublicPrefixContextStart savedInput (none :: savedOutput) publicBits tail instanceBits.length).rebasePc 23) := by
    simp only [Step, successors, next, Configuration.resumeAt]
    rw [hInput, hOutput]
    simp [preparePublicPrefixContext, skipUnary, skipFrame, Program.asSubroutine,
      Instruction.asSubroutine, savePublicPrefixContextStart, Configuration.rebasePc,
      before, publicBits, frame, encodeSecurityParameter, List.reverse_append,
      List.map_append, List.append_assoc, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, List.replicate_succ]
  have hSave := (savePublicPrefixContext_runs savedInput (none :: savedOutput) publicBits tail instanceBits.length).withSubroutine_halted_of_closed
    ([.moveRight .output] ++ a ++ b ++ [.moveRight .output]) savePublicPrefix [.halt] 41
    (by change 0 < 17; decide) rfl rfl savePublicPrefix_control_closed
  change RunsFor preparePublicPrefixContext
    ((savePublicPrefixContextStart savedInput (none :: savedOutput) publicBits tail instanceBits.length).rebasePc 23)
    ((preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail).resumeAt 41)
    (savePublicPrefixSteps publicBits) at hSave
  have hHalt : Step preparePublicPrefixContext
      ((preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail).resumeAt 41)
      (preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail) := by
    simp [Step, successors, next, preparePublicPrefixContext, skipUnary, skipFrame,
      savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, preparePublicPrefixContextFinish,
      savePublicPrefixContextFinish, Instruction.next]
  simpa only [preparePublicPrefixContextSteps, publicBits, Nat.add_assoc, Nat.zero_add] using
    RunsFor.succ ((RunsFor.succ (((RunsFor.succ (RunsFor.zero _) hMove).trans hUnary).trans hFrame) hAfter).trans hSave) hHalt

theorem preparePublicPrefixContext_runs (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) :
    RunsFor preparePublicPrefixContext
      (preparePublicPrefixContextStart savedInput savedOutput n instanceBits tail)
      (preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail)
      (preparePublicPrefixContextSteps n instanceBits) := by
  simpa [preparePublicPrefixContextPaddedStart, preparePublicPrefixContextStart] using
    preparePublicPrefixContextPadded_runs savedInput savedOutput n instanceBits tail 0 (Nat.zero_le _)

theorem preparePublicPrefixContext_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ preparePublicPrefixContext := by
  simp [preparePublicPrefixContext, skipUnary, skipFrame, savePublicPrefix,
    rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem preparePublicPrefixContext_eval (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) :
    evalConfigWithin preparePublicPrefixContext
      (preparePublicPrefixContextStart savedInput savedOutput n instanceBits tail)
      (preparePublicPrefixContextSteps n instanceBits) =
      PMF.pure (preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail) :=
  (preparePublicPrefixContext_runs savedInput savedOutput n instanceBits tail).evalConfigWithin_eq_pure_of_no_randomBit
    preparePublicPrefixContext_no_randomBit

/-- The new input prefix follows its real blank separator and the saved
source-call scratch data. All counter padding has been consumed by copying. -/
theorem preparePublicPrefixContextFinish_layout (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (tail : List (Option Bool)) :
    preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tail =
      { pc := 41,
        inputTape := {
          left := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: savedInput
          current := some true
          right := tail },
        outputTape := {
          left := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: savedOutput },
        halted := true } := by
  have hPadding : instanceBits.length - (encodeSecurityParameter n ++ frame instanceBits).length = 0 := by
    simp [encodeSecurityParameter, frame]
    omega
  simp only [List.length_append] at hPadding
  simp [preparePublicPrefixContextFinish, savePublicPrefixContextFinish, hPadding]

theorem preparePublicPrefixContextSteps_le (n : Nat) (instanceBits : List Bool) :
    preparePublicPrefixContextSteps n instanceBits ≤
      20 * (encodeSecurityParameter n ++ frame instanceBits).length + 30 := by
  have hSave := savePublicPrefixSteps_le (encodeSecurityParameter n ++ frame instanceBits)
  simp only [preparePublicPrefixContextSteps, encodeSecurityParameter, frame,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil] at *
  omega

set_option maxHeartbeats 600000 in
theorem preparePublicPrefixContext_control_closed (c d : Configuration)
    (hPc : c.pc < preparePublicPrefixContext.length) (step : Step preparePublicPrefixContext c d)
    (_hRunning : d.halted = false) : d.pc < preparePublicPrefixContext.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 42 at hPc
  change d.pc < 42
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, preparePublicPrefixContext,
    skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The contextual public-prefix front end stops on every finite input
tape. Native output moves reserve the counter's separator, so retained
caller cells stay behind a blank even when the input fields are malformed.
The actual restored input head is a true bit; subsequent cells need not
form a well-formed DDH field or a contiguous bitstring. -/
theorem preparePublicPrefixContext_terminates_with_suffix_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used savedInput afterOutput remaining,
      used ≤ 1000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 1000 ∧
      RunsFor preparePublicPrefixContext
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape.current = some true ∧
      finish.inputTape.left = savedInput ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remaining none } ∧
      ∃ count, finish.inputTape.right = input.right.drop count := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  let advanced : Tape := { left := none :: savedOutput, right := List.replicate (blanks - 1) none }
  have hAdvance : output.moveRight = advanced := by
    cases blanks <;> simp [output, advanced, Tape.moveRight, List.replicate_succ]
  obtain ⟨unary, unaryTime, hUnaryTime, hUnaryRun, hUnaryHalt, hUnaryOutput⟩ :=
    skipUnary_terminates_from_anyTape input advanced
  obtain ⟨framed, frameTime, frameSaved, frameBlanks, hFrameTime, hFrameRun, hFrameHalt, hFrameOutput⟩ :=
    skipFrameCells_terminates_with_layout unary.inputTape savedOutput (blanks - 1)
  obtain ⟨saved, saveTime, savedInput, afterOutput, remaining,
    hSaveTime, hSaveRun, hSaveHalt, hSaveInput, hSaveOutput⟩ :=
    savePublicPrefix_terminates_with_layout framed.inputTape (none :: frameSaved) (frameBlanks - 1)
  let a := skipUnary.asSubroutine 1 8
  let b := skipFrame.asSubroutine 8 22
  let k := savePublicPrefix.asSubroutine 23 41
  let start : Configuration := { inputTape := input, outputTape := output }
  let moved : Configuration := { pc := 1, inputTape := input, outputTape := advanced }
  have hMove : Step preparePublicPrefixContext start moved := by
    simp [Step, successors, next, preparePublicPrefixContext, start, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance, hAdvance]
  have hUnary := hUnaryRun.withSubroutine_halted_of_closed
    [.moveRight .output] skipUnary (b ++ [.moveRight .output] ++ k ++ [.halt]) 8
    (by change 0 < 6; decide) rfl hUnaryHalt skipUnary_control_closed
  change RunsFor preparePublicPrefixContext moved (unary.resumeAt 8) unaryTime at hUnary
  have hFrame := hFrameRun.withSubroutine_halted_of_closed
    ([.moveRight .output] ++ a) skipFrame ([.moveRight .output] ++ k ++ [.halt]) 22
    (by change 0 < 13; decide) rfl hFrameHalt skipFrame_control_closed
  have hFrameEntry :
      ({ inputTape := unary.inputTape, outputTape := advanced } : Configuration).rebasePc 8 =
      unary.resumeAt 8 := by
    simp only [Configuration.rebasePc, Configuration.resumeAt, hUnaryOutput, Nat.add_zero]
  change RunsFor preparePublicPrefixContext
    (({ inputTape := unary.inputTape, outputTape := advanced } : Configuration).rebasePc 8)
    (framed.resumeAt 22) frameTime at hFrame
  rw [hFrameEntry] at hFrame
  let afterMove : Configuration := { pc := 23, inputTape := framed.inputTape, outputTape := framed.outputTape.moveRight }
  have hAfterMove : Step preparePublicPrefixContext (framed.resumeAt 22) afterMove := by
    simp [Step, successors, next, preparePublicPrefixContext, skipUnary, skipFrame,
      Program.asSubroutine, Instruction.asSubroutine, afterMove, Configuration.resumeAt,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSaveEntry :
      ({ inputTape := framed.inputTape,
         outputTape := { left := none :: frameSaved, right := List.replicate (frameBlanks - 1) none } } : Configuration).rebasePc 23 =
      afterMove := by
    cases frameBlanks <;> simp [afterMove, Configuration.rebasePc, hFrameOutput, Tape.moveRight, List.replicate_succ]
  have hSave := hSaveRun.withSubroutine_halted_of_closed
    ([.moveRight .output] ++ a ++ b ++ [.moveRight .output]) savePublicPrefix [.halt] 41
    (by change 0 < 17; decide) rfl hSaveHalt savePublicPrefix_control_closed
  change RunsFor preparePublicPrefixContext
    (({ inputTape := framed.inputTape,
        outputTape := { left := none :: frameSaved, right := List.replicate (frameBlanks - 1) none } } : Configuration).rebasePc 23)
    (saved.resumeAt 41) saveTime at hSave
  rw [hSaveEntry] at hSave
  let finish : Configuration := { saved with pc := 41, halted := true }
  have hHalt : Step preparePublicPrefixContext (saved.resumeAt 41) finish := by
    simp [Step, successors, next, preparePublicPrefixContext, skipUnary, skipFrame,
      savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, finish, Configuration.resumeAt, Instruction.next]
  refine ⟨finish, 1 + unaryTime + frameTime + 1 + saveTime + 1,
    savedInput, afterOutput, remaining, ?_,
    RunsFor.succ ((RunsFor.succ (((RunsFor.succ (RunsFor.zero _) hMove).trans hUnary).trans hFrame) hAfterMove).trans hSave) hHalt,
    rfl, ?_, ?_, hSaveOutput, ?_⟩
  · have hUnaryStorage := GuardedCompiler.sourceStorage_le_of_run hUnaryRun
    have hFrameStorage := GuardedCompiler.sourceStorage_le_of_run hFrameRun
    have hMovedCells : advanced.cells ≤ output.cells + 1 := by
      rw [← hAdvance]
      exact Tape.cells_moveRight_le output
    have hFrameLeft : framed.inputTape.left.length ≤ framed.inputTape.cells := by
      dsimp only [Tape.cells]; omega
    dsimp only [GuardedCompiler.sourceStorage] at hUnaryStorage hFrameStorage
    change unary.inputTape.cells + unary.outputTape.cells ≤ input.cells + advanced.cells + unaryTime at hUnaryStorage
    change framed.inputTape.cells + framed.outputTape.cells ≤ unary.inputTape.cells + advanced.cells + frameTime at hFrameStorage
    change _ ≤ 1000 * (input.cells + output.cells) + 1000
    omega
  · change saved.inputTape.current = some true
    rw [hSaveInput]
  · change saved.inputTape.left = savedInput
    rw [hSaveInput]
  · obtain ⟨unaryCount, hUnaryRight⟩ := skipUnary_input_right_suffix hUnaryRun
    obtain ⟨frameCount, hFrameRight⟩ := skipFrame_input_right_suffix hFrameRun
    refine ⟨unaryCount + frameCount, ?_⟩
    change saved.inputTape.right = _
    simp only [hSaveInput, hFrameRight, hUnaryRight, List.drop_drop]

/-- All-input stopping and output-frontier certificate, with no frame
validity hypothesis. The stronger suffix theorem also records the cells
remaining to the right of the input head. -/
theorem preparePublicPrefixContext_terminates_with_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used savedInput afterOutput remaining,
      used ≤ 1000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 1000 ∧
      RunsFor preparePublicPrefixContext
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape.current = some true ∧
      finish.inputTape.left = savedInput ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remaining none } := by
  obtain ⟨finish, used, savedInput, afterOutput, remaining,
    hBound, hRun, hHalted, hCurrent, hLeft, hOutput, _hSuffix⟩ :=
    preparePublicPrefixContext_terminates_with_suffix_layout input savedOutput blanks
  exact ⟨finish, used, savedInput, afterOutput, remaining, hBound, hRun, hHalted, hCurrent, hLeft, hOutput⟩

/-- Native public-prefix assembly also stops when the output counter region
contains arbitrary finite cells. This stopping statement does not claim
that malformed caller data provides a fresh region for a guarded call. -/
theorem preparePublicPrefixContext_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 100000 * (input.cells + output.cells) + 100000 ∧
      RunsFor preparePublicPrefixContext
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨unary, unaryTime, hUnaryTime, unaryRun, unaryHalt, _unaryOutput⟩ :=
    skipUnary_terminates_from_anyTape input output.moveRight
  obtain ⟨framed, frameTime, hFrameTime, frameRun, frameHalt⟩ :=
    skipFrame_terminates_from_anyTape unary.inputTape unary.outputTape
  obtain ⟨saved, saveTime, hSaveTime, saveRun, saveHalt⟩ :=
    savePublicPrefix_terminates_from_anyTape framed.inputTape framed.outputTape.moveRight
  let moved : Configuration := { pc := 1, inputTape := input, outputTape := output.moveRight }
  have first : Step preparePublicPrefixContext
      ({ inputTape := input, outputTape := output } : Configuration) moved := by
    have code : preparePublicPrefixContext[0]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hUnary := unaryRun.withSubroutine_halted_of_closed
    [.moveRight .output] skipUnary
    (skipFrame.asSubroutine 8 22 ++ [.moveRight .output] ++ savePublicPrefix.asSubroutine 23 41 ++ [.halt]) 8
    (by change 0 < 6; decide) rfl unaryHalt skipUnary_control_closed
  change RunsFor preparePublicPrefixContext moved (unary.resumeAt 8) unaryTime at hUnary
  have leading := (RunsFor.succ (RunsFor.zero _) first).trans hUnary
  have hFrame := frameRun.withSubroutine_halted_of_closed
    ([.moveRight .output] ++ skipUnary.asSubroutine 1 8) skipFrame
    ([.moveRight .output] ++ savePublicPrefix.asSubroutine 23 41 ++ [.halt]) 22
    (by change 0 < 13; decide) rfl frameHalt skipFrame_control_closed
  change RunsFor preparePublicPrefixContext (unary.resumeAt 8) (framed.resumeAt 22) frameTime at hFrame
  let afterMove : Configuration := { pc := 23, inputTape := framed.inputTape, outputTape := framed.outputTape.moveRight }
  have move : Step preparePublicPrefixContext (framed.resumeAt 22) afterMove := by
    have code : preparePublicPrefixContext[22]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, afterMove, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have toSave := RunsFor.succ (leading.trans hFrame) move
  have hSave := saveRun.withSubroutine_halted_of_closed
    ([.moveRight .output] ++ skipUnary.asSubroutine 1 8 ++ skipFrame.asSubroutine 8 22 ++ [.moveRight .output])
    savePublicPrefix [.halt] 41
    (by change 0 < 17; decide) rfl saveHalt savePublicPrefix_control_closed
  change RunsFor preparePublicPrefixContext afterMove (saved.resumeAt 41) saveTime at hSave
  let finish : Configuration := { saved with pc := 41, halted := true }
  have last : Step preparePublicPrefixContext (saved.resumeAt 41) finish := by
    have code : preparePublicPrefixContext[41]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, 1 + unaryTime + frameTime + 1 + saveTime + 1, ?_,
    RunsFor.succ (toSave.trans hSave) last, rfl⟩
  have storageUnary := GuardedCompiler.sourceStorage_le_of_run leading
  have storageFramed := GuardedCompiler.sourceStorage_le_of_run (leading.trans hFrame)
  change unary.inputTape.cells + unary.outputTape.cells ≤ input.cells + output.cells + (1 + unaryTime) at storageUnary
  change framed.inputTape.cells + framed.outputTape.cells ≤ input.cells + output.cells + (1 + unaryTime + frameTime) at storageFramed
  have outputMove := Tape.cells_moveRight_le output
  have frameMove := Tape.cells_moveRight_le framed.outputTape
  omega

end Machine
