import Foundation.Machine.SelectedInputRestoration
import Foundation.Machine.ContextualPrefix

namespace Machine

/-- Begin assembling the certified multiplication input from stored cells.
Restore the DDH input, reserve a blank after the selected message, and copy
its public parameter/instance prefix into the new argument region. The
message and native challenge stay saved. This stage does not yet frame the
two element operands or invoke the multiplication certificate. -/
def prepareMultiplyPrefix : Program :=
  restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output] ++
    preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]

def prepareMultiplyPrefixStart (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  restoreStoredInputStart beforeInput
    (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail) reply consumed current right
    { left := selected.reverse.map some ++ beforeOutput, right := [none] }

def prepareMultiplyPrefixFinish (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { preparePublicPrefixContextFinish beforeInput (none :: selected.reverse.map some ++ beforeOutput)
      n instanceBits (tupleTail.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right)
      with pc := 63 }

def prepareMultiplyPrefixSteps (n : Nat) (instanceBits tupleTail reply consumed : List Bool) : Nat :=
  restoreStoredInputSteps (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail) reply consumed + 1 +
    preparePublicPrefixContextSteps n instanceBits + 1

/-- Full native trace: retained DDH cells are reached by charged rewinds and
then copied by the existing contextual prefix routine. Every saved tape cell
and the fresh argument region occur in the complete resulting configuration. -/
theorem prepareMultiplyPrefix_runs (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    RunsFor prepareMultiplyPrefix
      (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed) := by
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
  let output : Tape := { left := selected.reverse.map some ++ beforeOutput, right := [none] }
  let restored := restoreStoredInputFinish beforeInput original reply consumed current right output
  let tail := tupleTail.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right
  let prefixStart := preparePublicPrefixContextStart beforeInput
    (none :: selected.reverse.map some ++ beforeOutput) n instanceBits tail
  have hRestore := (restoreStoredInput_runs beforeInput original reply consumed current right output).withSubroutine_halted_of_closed
    [] restoreStoredInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor prepareMultiplyPrefix
    (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
    (restored.resumeAt 19) (restoreStoredInputSteps original reply consumed) at hRestore
  have hMove : Step prepareMultiplyPrefix (restored.resumeAt 19) (prefixStart.rebasePc 20) := by
    cases n <;> simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput,
      rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
      restored, restoreStoredInputFinish, prefixStart, preparePublicPrefixContextStart,
      skipUnaryCellsStart_layout, Configuration.resumeAt, Configuration.rebasePc,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      output, original, tail, encodeSecurityParameter, List.map_append, List.map_replicate,
      List.append_assoc, List.replicate_succ, Tape.moveRight]
  have hPrefix := (preparePublicPrefixContext_runs beforeInput
      (none :: selected.reverse.map some ++ beforeOutput) n instanceBits tail).withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 63
    (by change 0 < 42; decide) rfl rfl
    preparePublicPrefixContext_control_closed
  change RunsFor prepareMultiplyPrefix (prefixStart.rebasePc 20)
    ((prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).resumeAt 63)
    (preparePublicPrefixContextSteps n instanceBits) at hPrefix
  have hHalt : Step prepareMultiplyPrefix
      ((prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).resumeAt 63)
      (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right) := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput, preparePublicPrefixContext,
      rewindBitstring, skipUnary, skipFrame, savePublicPrefix, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, prepareMultiplyPrefixFinish,
      preparePublicPrefixContextFinish, savePublicPrefixContextFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((RunsFor.succ hRestore hMove).trans hPrefix) hHalt

theorem prepareMultiplyPrefix_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareMultiplyPrefix := by
  simp [prepareMultiplyPrefix, restoreStoredInput, preparePublicPrefixContext, rewindBitstring,
    skipUnary, skipFrame, savePublicPrefix, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem prepareMultiplyPrefix_eval (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    evalConfigWithin prepareMultiplyPrefix
      (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed) =
      PMF.pure (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right) :=
  (prepareMultiplyPrefix_runs beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).evalConfigWithin_eq_pure_of_no_randomBit
    prepareMultiplyPrefix_no_randomBit


/-- The new arithmetic argument region contains the public prefix, while
its two reserved blanks separate it from the saved selected element code.
No bit of the stored native challenge or earlier caller scratch is erased. -/
theorem prepareMultiplyPrefixFinish_output (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++
          none :: none :: selected.reverse.map some ++ beforeOutput } := by
  simp only [prepareMultiplyPrefixFinish]
  rw [preparePublicPrefixContextFinish_layout]
  simp [List.append_assoc]

/-- Restoring and copying public input costs linearly many native steps in
all retained input blocks. This bound makes no assumption about monotonicity
of a later group-operation budget. -/
theorem prepareMultiplyPrefix_steps_le (n : Nat) (instanceBits tupleTail reply consumed : List Bool) :
    prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed ≤
      22 * ((encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length +
        reply.length + consumed.length + 1) + 30 := by
  have hPrefix := preparePublicPrefixContextSteps_le n instanceBits
  have hLength : (encodeSecurityParameter n ++ frame instanceBits).length ≤
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length := by
    simp
  simp only [prepareMultiplyPrefixSteps, restoreStoredInputSteps]
  omega

/-- The actual selected-message return is the caller input for this native
arithmetic-prefix stage. The selected message code is neither re-decoded nor
loaded onto another tape; it remains in its original copied cells. -/
theorem selectedMessage_multiplyPrefix_layout (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply first second state : List Bool) (blanks : Nat) (bit : Bool) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
    returned.resumeAt 0 = prepareMultiplyPrefixStart before (none :: some bit :: beforeOutput)
      n instanceBits tupleTail reply (selectedMessageConsumed first second bit) (if bit then second else first)
      returned.inputTape.current returned.inputTape.right := by
  dsimp only
  rw [prepareSelectedMessageFinish_restore_layout]
  simp only [prepareMultiplyPrefixStart, prepareSelectedMessageFinish_output]

/-- Restore and copy the public prefix without assuming valid DDH input or
a canonical choose response. The caller supplies only a fresh output
frontier. Native restoration may reach an unintended malformed block, but
the contextual parser still stops and produces a fresh request frontier. -/
theorem prepareMultiplyPrefix_terminates_with_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 200000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 200000 ∧
      RunsFor prepareMultiplyPrefix
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreStoredInput_terminates_from_anyTape input output
  obtain ⟨copied, copyTime, _savedInput, after, remaining, hCopyTime, copyRun,
    copyHalt, _hInput, _hLeft, copyOutput⟩ :=
    preparePublicPrefixContext_terminates_with_layout restored.inputTape
      (none :: savedOutput) (blanks - 1)
  have hAdvance : output.moveRight =
      { left := none :: savedOutput, right := List.replicate (blanks - 1) none } := by
    cases blanks <;> simp [output, Tape.moveRight, List.replicate_succ]
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor prepareMultiplyPrefix
    ({ inputTape := input, outputTape := output } : Configuration)
    (restored.resumeAt 19) restoreTime at hRestore
  let start : Configuration :=
    { pc := 20, inputTape := restored.inputTape, outputTape := output.moveRight }
  have hMove : Step prepareMultiplyPrefix (restored.resumeAt 19) start := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, start, Configuration.resumeAt,
      restoreOutput, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hCopy := copyRun.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 63
    (by change 0 < 42; decide) rfl copyHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareMultiplyPrefix
    ({ pc := 20, inputTape := restored.inputTape,
       outputTape := { left := none :: savedOutput, right := List.replicate (blanks - 1) none } } : Configuration)
    (copied.resumeAt 63) copyTime at hCopy
  rw [← hAdvance] at hCopy
  change RunsFor prepareMultiplyPrefix start (copied.resumeAt 63) copyTime at hCopy
  let finish : Configuration := { copied with pc := 63, halted := true }
  have hStop : Step prepareMultiplyPrefix (copied.resumeAt 63) finish := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput,
      preparePublicPrefixContext, rewindBitstring, skipUnary, skipFrame, savePublicPrefix,
      copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + 1 + copyTime + 1, after, remaining, ?_,
    RunsFor.succ ((RunsFor.succ hRestore hMove).trans hCopy) hStop, rfl, copyOutput⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
  have hMoved := Tape.cells_moveRight_le output
  rw [← hAdvance] at hCopyTime
  change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
  change copyTime ≤ 1000 * (restored.inputTape.cells + output.moveRight.cells) + 1000 at hCopyTime
  rw [restoreOutput] at hStorage
  change _ ≤ 200000 * (input.cells + output.cells) + 200000
  omega

end Machine
