import Foundation.Machine.SegmentCopy
import Foundation.Machine.TapeSwap
import Foundation.Machine.UnaryInput
import Foundation.Machine.FramedInput
import Foundation.Machine.GuardedTrace

namespace Machine

/-- Save the contiguous public prefix immediately left of a known true
header bit onto the fresh output region. The header is temporarily erased
as a separator, then restored by a charged write. The following tuple cells
are never copied or overwritten. This routine is invoked at a validated
header boundary; it is not a standalone arbitrary-input parser. -/
def savePublicPrefix : Program :=
  [.erase .input] ++ rewindBitstring.asSubroutine 1 6 ++
    copyBitstring.asSubroutine 6 15 ++ [.write .input true, .halt]

def savePublicPrefixStart (publicBits : List Bool) (tail beforeOutput : List (Option Bool))
    (blanks : Nat) : Configuration :=
  { inputTape := { left := publicBits.reverse.map some, current := some true, right := tail },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

/-- Exact physical result. The rewind can materialize an outer blank to
its left; that cell is retained. The header and all following tuple cells
have their original values, while the output head follows the copied prefix. -/
def savePublicPrefixFinish (publicBits : List Bool) (tail beforeOutput : List (Option Bool))
    (blanks : Nat) : Configuration :=
  { pc := 16,
    inputTape := { left := publicBits.reverse.map some ++ [none], current := some true, right := tail },
    outputTape := {
      left := publicBits.reverse.map some ++ beforeOutput
      right := List.replicate (blanks - publicBits.length) none },
    halted := true }

def savePublicPrefixSteps (publicBits : List Bool) : Nat :=
  1 + (2 * publicBits.length + 4) + copyBitstringSteps publicBits + 2

theorem savePublicPrefix_runs (publicBits : List Bool) (tail beforeOutput : List (Option Bool))
    (blanks : Nat) :
    RunsFor savePublicPrefix (savePublicPrefixStart publicBits tail beforeOutput blanks)
      (savePublicPrefixFinish publicBits tail beforeOutput blanks) (savePublicPrefixSteps publicBits) := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let erased : Configuration :=
    { pc := 1, inputTape := { left := publicBits.reverse.map some, right := tail }, outputTape := output }
  let rewound : Configuration :=
    { pc := 3, inputTape := ({ right := publicBits.map some ++ none :: tail } : Tape).moveRight,
      outputTape := output, halted := true }
  have hErase : Step savePublicPrefix (savePublicPrefixStart publicBits tail beforeOutput blanks) erased := by
    simp [Step, successors, next, savePublicPrefix, savePublicPrefixStart, erased, output,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write]
  have hRewind := (rewindBitstring_runs_from publicBits none tail output).withSubroutine_halted_of_closed
    [.erase .input] rewindBitstring
    (copyBitstring.asSubroutine 6 15 ++ [.write .input true, .halt]) 6
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor savePublicPrefix erased (rewound.resumeAt 6) (2 * publicBits.length + 4) at hRewind
  have hCopyStart : rewound.resumeAt 6 =
      (copySegmentStart [none] beforeOutput tail publicBits blanks).rebasePc 6 := by
    cases publicBits <;> simp [rewound, copySegmentStart_layout,
      Configuration.resumeAt, Configuration.rebasePc, output, Tape.moveRight]
  rw [hCopyStart] at hRewind
  have hCopy := (copySegment_runs [none] beforeOutput tail publicBits blanks).withSubroutine_halted_of_closed
    ([.erase .input] ++ rewindBitstring.asSubroutine 1 6) copyBitstring
    [.write .input true, .halt] 15
    (by change 0 < 8; decide) rfl rfl GuardedCompiler.copyBitstring_control_closed
  change RunsFor savePublicPrefix
    ((copySegmentStart [none] beforeOutput tail publicBits blanks).rebasePc 6)
    ((copySegmentFinish [none] beforeOutput tail publicBits blanks).resumeAt 15)
    (copyBitstringSteps publicBits) at hCopy
  let written : Configuration :=
    { savePublicPrefixFinish publicBits tail beforeOutput blanks with halted := false }
  have hWrite : Step savePublicPrefix
      ((copySegmentFinish [none] beforeOutput tail publicBits blanks).resumeAt 15) written := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, copySegmentFinish,
      Configuration.resumeAt, written, savePublicPrefixFinish, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.write]
  have hHalt : Step savePublicPrefix written
      (savePublicPrefixFinish publicBits tail beforeOutput blanks) := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, written, savePublicPrefixFinish, Instruction.next]
  simpa only [savePublicPrefixSteps, Nat.add_assoc, Nat.zero_add, Nat.reduceAdd] using
    RunsFor.succ (RunsFor.succ (((RunsFor.succ (RunsFor.zero _) hErase).trans hRewind).trans hCopy)
      hWrite) hHalt

theorem savePublicPrefixSteps_le (publicBits : List Bool) :
    savePublicPrefixSteps publicBits ≤ 8 * publicBits.length + 9 := by
  have hCopy := copyBitstringSteps_le publicBits
  simp only [savePublicPrefixSteps]
  omega

theorem savePublicPrefix_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ savePublicPrefix := by
  simp [savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem savePublicPrefix_eval (publicBits : List Bool) (tail beforeOutput : List (Option Bool))
    (blanks : Nat) :
    evalConfigWithin savePublicPrefix (savePublicPrefixStart publicBits tail beforeOutput blanks)
      (savePublicPrefixSteps publicBits) = PMF.pure (savePublicPrefixFinish publicBits tail beforeOutput blanks) :=
  (savePublicPrefix_runs publicBits tail beforeOutput blanks).evalConfigWithin_eq_pure_of_no_randomBit
    savePublicPrefix_no_randomBit

/-- The finite copying routine returns from each embedded block before its
final explicit halt. This control fact is independent of the tape contents. -/
theorem savePublicPrefix_control_closed (c d : Configuration)
    (hPc : c.pc < savePublicPrefix.length) (step : Step savePublicPrefix c d)
    (_hRunning : d.halted = false) : d.pc < savePublicPrefix.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 17 at hPc
  change d.pc < 17
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, savePublicPrefix,
    rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Stopping bound for saving a prefix on arbitrary finite caller tapes.
Malformed boundaries and internal blanks can change which cells are copied;
the assertion concerns the actual native execution, not successful parsing. -/
theorem savePublicPrefix_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 20 * (input.cells + output.cells) + 33 ∧
      RunsFor savePublicPrefix
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  let erased : Tape := input.write none
  obtain ⟨rewound, rewindTime, hRewindTime, hRewindRun, hRewindHalt, _⟩ :=
    rewindBitstring_terminates_from erased output
  obtain ⟨copied, copyTime, hCopyTime, hCopyRun, hCopyHalt⟩ :=
    copyBitstring_terminates_from_anyTape rewound.inputTape rewound.outputTape
  have hErase : Step savePublicPrefix
      ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 1, inputTape := erased, outputTape := output } : Configuration) := by
    simp [Step, successors, next, savePublicPrefix, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    [.erase .input] rewindBitstring
    (copyBitstring.asSubroutine 6 15 ++ [.write .input true, .halt]) 6
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor savePublicPrefix
    ({ pc := 1, inputTape := erased, outputTape := output } : Configuration)
    (rewound.resumeAt 6) rewindTime at hRewind
  have hCopy := hCopyRun.withSubroutine_halted_of_closed
    ([.erase .input] ++ rewindBitstring.asSubroutine 1 6) copyBitstring
    [.write .input true, .halt] 15
    (by change 0 < 8; decide) rfl hCopyHalt GuardedCompiler.copyBitstring_control_closed
  change RunsFor savePublicPrefix
    ({ pc := 6, inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration)
    (copied.resumeAt 15) copyTime at hCopy
  have hCopyStart : rewound.resumeAt 6 =
      ({ pc := 6, inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration) := rfl
  rw [← hCopyStart] at hCopy
  let written : Configuration :=
    { pc := 16, inputTape := copied.inputTape.write (some true), outputTape := copied.outputTape }
  have hWrite : Step savePublicPrefix (copied.resumeAt 15) written := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step savePublicPrefix written { written with halted := true } := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, written, Instruction.next]
  refine ⟨{ written with halted := true }, 1 + rewindTime + copyTime + 2, ?_, ?_, rfl⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run hRewindRun
    simp only [GuardedCompiler.sourceStorage] at hStorage
    have hCells : erased.cells = input.cells := Tape.cells_write input none
    have hLeft : erased.left.length ≤ input.cells := by
      simp only [erased, Tape.write, Tape.cells]
      omega
    change rewound.inputTape.cells + rewound.outputTape.cells ≤ erased.cells + output.cells + rewindTime at hStorage
    omega
  · simpa only [Nat.add_assoc, Nat.zero_add, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ
        (((RunsFor.succ (RunsFor.zero _) hErase).trans hRewind).trans hCopy) hWrite) hHalt

/-- Saving the nearest contiguous prefix retains all cells to the right
of the caller's current head and leaves a fresh output region. This also
covers malformed parser boundaries and arbitrary saved cells to the left;
only the actual rewind and copy instructions determine the copied block. -/
theorem savePublicPrefix_terminates_with_layout (input : Tape)
    (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput afterOutput : List (Option Bool))
      (remainingBlanks : Nat),
      used ≤ 8 * input.left.length + 9 ∧
      RunsFor savePublicPrefix
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := beforeInput, current := some true, right := input.right } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingBlanks none } := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let erased : Tape := input.write none
  obtain ⟨rewound, bits, saved, hLength, hRewindRun, hRewindHalt, hRewindInput, hRewindOutput⟩ :=
    rewindBitstring_terminates_with_layout erased output
  have hErase : Step savePublicPrefix
      ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 1, inputTape := erased, outputTape := output } : Configuration) := by
    simp [Step, successors, next, savePublicPrefix, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    [.erase .input] rewindBitstring
    (copyBitstring.asSubroutine 6 15 ++ [.write .input true, .halt]) 6
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor savePublicPrefix
    ({ pc := 1, inputTape := erased, outputTape := output } : Configuration)
    (rewound.resumeAt 6) (2 * bits.length + 4) at hRewind
  have hCopyStart : rewound.resumeAt 6 =
      (copySegmentStart ([none] ++ saved) beforeOutput input.right bits blanks).rebasePc 6 := by
    simp only [Configuration.resumeAt, Configuration.rebasePc, copySegmentStart_layout,
      hRewindInput, hRewindOutput, erased, Tape.write, output]
  rw [hCopyStart] at hRewind
  have hCopy := (copySegment_runs ([none] ++ saved) beforeOutput input.right bits blanks).withSubroutine_halted_of_closed
      ([.erase .input] ++ rewindBitstring.asSubroutine 1 6) copyBitstring
      [.write .input true, .halt] 15
      (by change 0 < 8; decide) rfl rfl GuardedCompiler.copyBitstring_control_closed
  change RunsFor savePublicPrefix
    ((copySegmentStart ([none] ++ saved) beforeOutput input.right bits blanks).rebasePc 6)
    ((copySegmentFinish ([none] ++ saved) beforeOutput input.right bits blanks).resumeAt 15)
    (copyBitstringSteps bits) at hCopy
  let written : Configuration :=
    { pc := 16
      inputTape := { left := bits.reverse.map some ++ ([none] ++ saved), current := some true, right := input.right }
      outputTape := { left := bits.reverse.map some ++ beforeOutput, right := List.replicate (blanks - bits.length) none } }
  have hWrite : Step savePublicPrefix
      ((copySegmentFinish ([none] ++ saved) beforeOutput input.right bits blanks).resumeAt 15)
      written := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, copySegmentFinish, written,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.write]
  have hHalt : Step savePublicPrefix written { written with halted := true } := by
    simp [Step, successors, next, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, written, Instruction.next]
  refine ⟨{ written with halted := true }, savePublicPrefixSteps bits,
    bits.reverse.map some ++ ([none] ++ saved), bits.reverse.map some ++ beforeOutput,
    blanks - bits.length, ?_, ?_, rfl, rfl, rfl⟩
  · have hTime := savePublicPrefixSteps_le bits
    change bits.length ≤ input.left.length at hLength
    omega
  · simpa only [savePublicPrefixSteps, Nat.add_assoc, Nat.zero_add, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ
        (((RunsFor.succ (RunsFor.zero _) hErase).trans hRewind).trans hCopy) hWrite) hHalt

/-- Native preparation of the common public-input prefix for a DDH wrapper.
First scan the unary security parameter and the instance frame. Then copy
that exact prefix onto the opposite tape, retaining the following request.
The correctness fixture below starts with a true request header, as occurs
for every nonempty framed tuple. No instance-family oracle is used. -/
def prepareDDHPublicPrefix : Program :=
  skipUnary.asSubroutine 0 7 ++ skipFrame.asSubroutine 7 21 ++
    savePublicPrefix.asSubroutine 21 39 ++ [.halt]

def prepareDDHPublicPrefixSteps (n : Nat) (instanceBits : List Bool) : Nat :=
  (3 * n + 3) + (10 * instanceBits.length + 5) +
    savePublicPrefixSteps (encodeSecurityParameter n ++ frame instanceBits) + 1

def prepareDDHPublicPrefixFinish (n : Nat) (instanceBits requestTail : List Bool) : Configuration :=
  { savePublicPrefixFinish (encodeSecurityParameter n ++ frame instanceBits)
      (requestTail.map some) [] (instanceBits.length + 1) with pc := 39 }

/-- Exact machine trace on a framed current input. The request header is
restored and the entire request tail survives. The output contains only the
copied public prefix; it is now ready for assembly of the choose request. -/
theorem prepareDDHPublicPrefix_runs (n : Nat) (instanceBits requestTail : List Bool) :
    RunsFor prepareDDHPublicPrefix
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail))
      (prepareDDHPublicPrefixFinish n instanceBits requestTail)
      (prepareDDHPublicPrefixSteps n instanceBits) := by
  let a := skipUnary.asSubroutine 0 7
  let b := skipFrame.asSubroutine 7 21
  let k := savePublicPrefix.asSubroutine 21 39
  let before := some false :: List.replicate n (some true)
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  have hUnary := (skipUnary_runs [] n (frame instanceBits ++ true :: requestTail) {}).withSubroutine_halted_of_closed
    [] skipUnary (b ++ k ++ [.halt]) 7
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  have hInitial : (skipUnaryStart [] n (frame instanceBits ++ true :: requestTail) {}).rebasePc 0 =
      Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail) := by
    simp only [List.append_assoc]
    cases hBits : encodeSecurityParameter n ++ (frame instanceBits ++ true :: requestTail) <;>
      simp [skipUnaryStart, Configuration.initial, Configuration.rebasePc, hBits, Tape.ofBits]
  change RunsFor prepareDDHPublicPrefix
    ((skipUnaryStart [] n (frame instanceBits ++ true :: requestTail) {}).rebasePc 0)
    ((skipUnaryFinish [] n (frame instanceBits ++ true :: requestTail) {}).resumeAt 7)
    (3 * n + 3) at hUnary
  rw [hInitial] at hUnary
  have hFrameStart : (skipUnaryFinish [] n (frame instanceBits ++ true :: requestTail) {}).resumeAt 7 =
      (skipFrameStart instanceBits.length (instanceBits ++ true :: requestTail) before).rebasePc 7 := by
    simp [skipUnaryFinish, skipFrameStart, Configuration.resumeAt, Configuration.rebasePc,
      before, frame, List.append_assoc]
  rw [hFrameStart] at hUnary
  change RunsFor prepareDDHPublicPrefix
    (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail))
    ((skipFrameStart instanceBits.length (instanceBits ++ true :: requestTail) before).rebasePc 7)
    (3 * n + 3) at hUnary
  have hFrame := (skipFrame_runs_from before instanceBits.length (instanceBits ++ true :: requestTail)).withSubroutine_halted_of_closed
    a skipFrame (k ++ [.halt]) 21
    (by change 0 < 13; decide) rfl rfl skipFrame_control_closed
  change RunsFor prepareDDHPublicPrefix
    ((skipFrameStart instanceBits.length (instanceBits ++ true :: requestTail) before).rebasePc 7)
    ((skipFrameFinish instanceBits.length (instanceBits ++ true :: requestTail) before).resumeAt 21)
    (10 * instanceBits.length + 5) at hFrame
  have hSaveStart : (skipFrameFinish instanceBits.length (instanceBits ++ true :: requestTail) before).resumeAt 21 =
      (savePublicPrefixStart publicBits (requestTail.map some) [] (instanceBits.length + 1)).rebasePc 21 := by
    have hInput := skipFrameFinish_input instanceBits (true :: requestTail) before
    have hOutput : (skipFrameFinish instanceBits.length (instanceBits ++ true :: requestTail) before).outputTape =
        ({ right := List.replicate (instanceBits.length + 1) none } : Tape) := rfl
    change ({
      pc := 21
      inputTape := (skipFrameFinish instanceBits.length (instanceBits ++ true :: requestTail) before).inputTape
      outputTape := (skipFrameFinish instanceBits.length (instanceBits ++ true :: requestTail) before).outputTape } : Configuration) = _
    rw [hInput, hOutput]
    simp [savePublicPrefixStart, Configuration.rebasePc, publicBits, before, frame,
      encodeSecurityParameter, List.reverse_append, List.map_append, List.append_assoc, Tape.ofBits]
  rw [hSaveStart] at hFrame
  have hSave := (savePublicPrefix_runs publicBits (requestTail.map some) [] (instanceBits.length + 1)).withSubroutine_halted_of_closed
    (a ++ b) savePublicPrefix [.halt] 39
    (by change 0 < 17; decide) rfl rfl savePublicPrefix_control_closed
  change RunsFor prepareDDHPublicPrefix
    ((savePublicPrefixStart publicBits (requestTail.map some) [] (instanceBits.length + 1)).rebasePc 21)
    ((prepareDDHPublicPrefixFinish n instanceBits requestTail).resumeAt 39)
    (savePublicPrefixSteps publicBits) at hSave
  have hHalt : Step prepareDDHPublicPrefix
      ((prepareDDHPublicPrefixFinish n instanceBits requestTail).resumeAt 39)
      (prepareDDHPublicPrefixFinish n instanceBits requestTail) := by
    simp [Step, successors, next, prepareDDHPublicPrefix, skipUnary, skipFrame,
      savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, prepareDDHPublicPrefixFinish,
      savePublicPrefixFinish, Instruction.next]
  simpa only [prepareDDHPublicPrefixSteps, Nat.add_assoc] using
    RunsFor.succ ((hUnary.trans hFrame).trans hSave) hHalt

theorem prepareDDHPublicPrefix_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareDDHPublicPrefix := by
  simp [prepareDDHPublicPrefix, skipUnary, skipFrame, savePublicPrefix,
    rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareDDHPublicPrefix_eval (n : Nat) (instanceBits requestTail : List Bool) :
    evalConfigWithin prepareDDHPublicPrefix
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail))
      (prepareDDHPublicPrefixSteps n instanceBits) =
      PMF.pure (prepareDDHPublicPrefixFinish n instanceBits requestTail) :=
  (prepareDDHPublicPrefix_runs n instanceBits requestTail).evalConfigWithin_eq_pure_of_no_randomBit
    prepareDDHPublicPrefix_no_randomBit

/-- Every move and copied cell is charged. The bound is linear in the
complete current input, and does not depend on a caller's source-code budget
or on an instance-family value available outside the tapes. -/
theorem prepareDDHPublicPrefixSteps_le (n : Nat) (instanceBits requestTail : List Bool) :
    prepareDDHPublicPrefixSteps n instanceBits ≤
      26 * (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail).length + 34 := by
  have hSave := savePublicPrefixSteps_le (encodeSecurityParameter n ++ frame instanceBits)
  simp only [prepareDDHPublicPrefixSteps, encodeSecurityParameter, frame, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] at *
  omega

theorem prepareDDHPublicPrefix_output (n : Nat) (instanceBits requestTail : List Bool) :
    (prepareDDHPublicPrefixFinish n instanceBits requestTail).outputBits =
      encodeSecurityParameter n ++ frame instanceBits := by
  simp [prepareDDHPublicPrefixFinish, savePublicPrefixFinish, Configuration.outputBits,
    Tape.bits, List.filterMap_append]

/-- Input data have their original values after the temporary separator is
restored. Only an unused outer blank may have been materialized by rewind. -/
theorem prepareDDHPublicPrefix_input (n : Nat) (instanceBits requestTail : List Bool) :
    (prepareDDHPublicPrefixFinish n instanceBits requestTail).inputTape.bits =
      encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail := by
  simp [prepareDDHPublicPrefixFinish, savePublicPrefixFinish, Tape.bits,
    List.reverse_append, List.filterMap_append, List.append_assoc]

theorem prepareDDHPublicPrefix_haltsWithin (n : Nat) (instanceBits requestTail : List Bool) :
    HaltsWithin prepareDDHPublicPrefix
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail)
      (26 * (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail).length + 34) := by
  have hHalts : HaltsWith prepareDDHPublicPrefix
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail)
      (encodeSecurityParameter n ++ frame instanceBits) (prepareDDHPublicPrefixSteps n instanceBits) :=
    ⟨_, prepareDDHPublicPrefix_runs n instanceBits requestTail, rfl,
      prepareDDHPublicPrefix_output n instanceBits requestTail⟩
  exact (hHalts.haltsWithin_of_no_randomBit prepareDDHPublicPrefix_no_randomBit).mono
    (prepareDDHPublicPrefixSteps_le n instanceBits requestTail)

/-- Every nonempty framed request starts with a true unary-header bit.
This specializes the actual preparation trace to the current protocol-input
format, while retaining the complete frame and its payload on the input tape. -/
theorem prepareDDHPublicPrefix_framed_eval (n : Nat) (instanceBits request : List Bool)
    (hNonempty : request ≠ []) :
    evalConfigWithin prepareDDHPublicPrefix
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame request))
      (prepareDDHPublicPrefixSteps n instanceBits) =
      PMF.pure (prepareDDHPublicPrefixFinish n instanceBits
        (List.replicate (request.length - 1) true ++ false :: request)) := by
  have hHeader : frame request =
      true :: (List.replicate (request.length - 1) true ++ false :: request) := by
    cases request with
    | nil => exact False.elim (hNonempty rfl)
    | cons bit rest => simp [frame, List.replicate_succ, List.append_assoc]
  rw [hHeader]
  exact prepareDDHPublicPrefix_eval _ _ _

/-- The fixed preparation block never exits except through its explicit
halt. This permits native caller composition using its exact proved trace. -/
theorem prepareDDHPublicPrefix_control_closed (c d : Configuration)
    (hPc : c.pc < prepareDDHPublicPrefix.length) (step : Step prepareDDHPublicPrefix c d)
    (_hRunning : d.halted = false) : d.pc < prepareDDHPublicPrefix.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 40 at hPc
  change d.pc < 40
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareDDHPublicPrefix,
    skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- All finite raw inputs stop in the native public-prefix preparation.
This includes missing unary delimiters, truncated frames, empty requests,
and arbitrary request tags. The bound charges all retained-tape work;
no successful protocol interpretation is asserted on malformed inputs. -/
theorem prepareDDHPublicPrefix_terminates_with_layout (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput : List (Option Bool))
      (rest : List Bool) (beforeOutput : List (Option Bool)) (blanks : Nat),
      used ≤ 300 * input.length + 300 ∧
      RunsFor prepareDDHPublicPrefix (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      finish.inputTape = { Tape.ofBits (true :: rest) with left := beforeInput } ∧
      finish.outputTape = { left := beforeOutput, right := List.replicate blanks none } := by
  obtain ⟨unaryFinish, unaryTime, before, rest, hUnaryTime, hRest, hUnaryRun,
    hUnaryHalt, hUnaryTape, hUnaryOutput⟩ := skipUnary_terminates_with_suffix [] input {}
  obtain ⟨frameFinish, frameTime, frameBefore, frameRest, frameOutput, frameBlanks,
    hFrameTime, hFrameRun, hFrameHalt, hFrameInput, hFrameOutput⟩ :=
    skipFrame_terminates_with_layout before rest
  obtain ⟨saveFinish, saveTime, saveBefore, saveOutput, saveBlanks,
    hSaveTime, hSaveRun, hSaveHalt, hSaveInput, hSaveOutput⟩ :=
    savePublicPrefix_terminates_with_layout frameFinish.inputTape frameOutput frameBlanks
  rw [← hFrameOutput] at hSaveRun
  let a := skipUnary.asSubroutine 0 7
  let b := skipFrame.asSubroutine 7 21
  let k := savePublicPrefix.asSubroutine 21 39
  have hUnary := hUnaryRun.withSubroutine_halted_of_closed
    [] skipUnary (b ++ k ++ [.halt]) 7
    (by change 0 < 6; decide) rfl hUnaryHalt skipUnary_control_closed
  have hInitial :
      (({ inputTape := { Tape.ofBits input with left := [] } } : Configuration).rebasePc 0) =
      Configuration.initial input := by
    cases input <;> rfl
  change RunsFor prepareDDHPublicPrefix
    (({ inputTape := { Tape.ofBits input with left := [] } } : Configuration).rebasePc 0)
    (unaryFinish.resumeAt 7) unaryTime at hUnary
  rw [hInitial] at hUnary
  have hFrame := hFrameRun.withSubroutine_halted_of_closed
    a skipFrame (k ++ [.halt]) 21
    (by change 0 < 13; decide) rfl hFrameHalt skipFrame_control_closed
  change RunsFor prepareDDHPublicPrefix
    (({ inputTape := { Tape.ofBits rest with left := before } } : Configuration).rebasePc 7)
    (frameFinish.resumeAt 21) frameTime at hFrame
  have hFrameStart : unaryFinish.resumeAt 7 =
      (({ inputTape := { Tape.ofBits rest with left := before } } : Configuration).rebasePc 7) := by
    simp only [Configuration.resumeAt, Configuration.rebasePc, hUnaryTape, hUnaryOutput]
  rw [← hFrameStart] at hFrame
  have hSave := hSaveRun.withSubroutine_halted_of_closed
    (a ++ b) savePublicPrefix [.halt] 39
    (by change 0 < 17; decide) rfl hSaveHalt savePublicPrefix_control_closed
  change RunsFor prepareDDHPublicPrefix
    (({ inputTape := frameFinish.inputTape, outputTape := frameFinish.outputTape } : Configuration).rebasePc 21)
    (saveFinish.resumeAt 39) saveTime at hSave
  have hSaveStart : frameFinish.resumeAt 21 =
      (({ inputTape := frameFinish.inputTape, outputTape := frameFinish.outputTape } : Configuration).rebasePc 21) := rfl
  rw [← hSaveStart] at hSave
  have hHalt : Step prepareDDHPublicPrefix (saveFinish.resumeAt 39)
      { saveFinish.resumeAt 39 with halted := true } := by
    simp [Step, successors, next, prepareDDHPublicPrefix, skipUnary, skipFrame,
      savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, Instruction.next]
  refine ⟨{ saveFinish.resumeAt 39 with halted := true }, unaryTime + frameTime + saveTime + 1,
    saveBefore, frameRest.tail, saveOutput, saveBlanks,
    ?_, RunsFor.succ ((hUnary.trans hFrame).trans hSave) hHalt, rfl, ?_, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run (hUnary.trans hFrame)
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hStorage
    have hInputCells : (Configuration.initial input).inputTape.cells ≤ input.length + 1 := by
      cases input
      · simp [Configuration.initial, Tape.ofBits, Tape.cells]
      · simp only [Configuration.initial, Tape.ofBits, Tape.cells, List.length_nil,
          List.length_map, List.length_cons]
        omega
    have hOutputCells : (Configuration.initial input).outputTape.cells = 1 := rfl
    have hLeft : frameFinish.inputTape.left.length ≤ frameFinish.inputTape.cells := by
      simp only [Tape.cells]
      omega
    omega
  · cases frameRest <;> simp only [Configuration.resumeAt, hSaveInput, hFrameInput, Tape.ofBits, List.tail, List.map_nil]
  · exact hSaveOutput

/-- All-input stopping follows from the physical layout certificate. -/
theorem prepareDDHPublicPrefix_terminates (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 300 * input.length + 300 ∧
      RunsFor prepareDDHPublicPrefix (Configuration.initial input) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, _, _, _, _, hBound, hRun, hHalted, _, _⟩ :=
    prepareDDHPublicPrefix_terminates_with_layout input
  exact ⟨finish, used, hBound, hRun, hHalted⟩

/-- Worst-case linear runtime of public-prefix preparation on every raw
bitstring. Determinism of the native block upgrades its stopping trace to
the universal branch bound required by the machine runtime definition. -/
theorem prepareDDHPublicPrefix_haltsWithin_anyInput (input : List Bool) :
    HaltsWithin prepareDDHPublicPrefix input (300 * input.length + 300) := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ := prepareDDHPublicPrefix_terminates input
  have hHalts : HaltsWith prepareDDHPublicPrefix input finish.outputBits used :=
    ⟨finish, hRun, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit prepareDDHPublicPrefix_no_randomBit).mono hBound

theorem prepareDDHPublicPrefix_polynomialTime : PolynomialTime prepareDDHPublicPrefix := by
  refine ⟨fun m => 300 * m + 300, ?_, prepareDDHPublicPrefix_haltsWithin_anyInput⟩
  exact ((PolynomiallyBounded.const 300).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 300)

end Machine
