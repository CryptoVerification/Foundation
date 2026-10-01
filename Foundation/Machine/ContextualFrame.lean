import Foundation.Machine.FramedOutput
import Foundation.Machine.SegmentCopy
import Foundation.Machine.GuardedTrace

namespace Machine

open GuardedCompiler

private def contextSegment (before : List (Option Bool)) (bits : List Bool)
    (tail : List (Option Bool)) : Tape :=
  { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with left := before }

private def contextHeaderState (savedInput beforeOutput tail : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := contextSegment (copied.reverse.map some ++ none :: savedInput) remaining tail,
    outputTape := {
      left := List.replicate copied.length (some true) ++ beforeOutput
      right := List.replicate (blanks - copied.length) none } }

private def contextHeaderFinish (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 7,
    inputTape := { left := bits.reverse.map some ++ none :: savedInput, right := tail },
    outputTape := {
      left := some false :: List.replicate bits.length (some true) ++ beforeOutput
      right := List.replicate (blanks - (bits.length + 1)) none },
    halted := true }

private theorem contextHeader_bit (savedInput beforeOutput tail : List (Option Bool))
    (copied rest : List Bool) (bit : Bool) (blanks : Nat) :
    RunsFor writeFrameHeader (contextHeaderState savedInput beforeOutput tail copied (bit :: rest) blanks)
      (contextHeaderState savedInput beforeOutput tail (copied ++ [bit]) rest blanks) 5 := by
  let start := contextHeaderState savedInput beforeOutput tail copied (bit :: rest) blanks
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration :=
    { selected with pc := 2, outputTape := selected.outputTape.write (some true) }
  let movedInput : Configuration :=
    { written with pc := 3, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hSelect : Step writeFrameHeader start selected := by
    cases bit <;> simp [Step, successors, next, writeFrameHeader, start, selected,
      contextHeaderState, contextSegment, Tape.moveRight, Instruction.next, Configuration.tape]
  have hWrite : Step writeFrameHeader selected written := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written,
      contextHeaderState, contextSegment, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step writeFrameHeader written movedInput := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, movedInput,
      contextHeaderState, contextSegment, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step writeFrameHeader movedInput movedOutput := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, movedInput,
      movedOutput, contextHeaderState, contextSegment, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step writeFrameHeader movedOutput
      (contextHeaderState savedInput beforeOutput tail (copied ++ [bit]) rest blanks) := by
    have hSub : blanks - (copied.length + 1) = (blanks - copied.length) - 1 := by omega
    cases hPad : blanks - copied.length <;> cases rest <;> simp [Step, successors, next, writeFrameHeader, start, selected, written,
      movedInput, movedOutput, contextHeaderState, contextSegment, Instruction.next, Tape.moveRight,
      Tape.write, List.reverse_append, List.replicate_succ, hSub, hPad]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hInput) hOutput) hBack

private theorem contextHeader_loop (savedInput beforeOutput tail : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) :
    RunsFor writeFrameHeader (contextHeaderState savedInput beforeOutput tail copied remaining blanks)
      (contextHeaderFinish savedInput beforeOutput tail (copied ++ remaining) blanks) (5 * remaining.length + 4) := by
  induction remaining generalizing copied with
  | nil =>
      let start := contextHeaderState savedInput beforeOutput tail copied [] blanks
      let selected : Configuration := { start with pc := 5 }
      let written : Configuration :=
        { selected with pc := 6, outputTape := selected.outputTape.write (some false) }
      let moved : Configuration :=
        { written with pc := 7, outputTape := written.outputTape.moveRight }
      have hSelect : Step writeFrameHeader start selected := by
        simp [Step, successors, next, writeFrameHeader, start, selected,
          contextHeaderState, contextSegment, Tape.moveRight, Instruction.next, Configuration.tape]
      have hWrite : Step writeFrameHeader selected written := by
        simp [Step, successors, next, writeFrameHeader, start, selected, written,
          contextHeaderState, contextSegment, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hMove : Step writeFrameHeader written moved := by
        simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
          contextHeaderState, contextSegment, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hSub : blanks - (copied.length + 1) = (blanks - copied.length) - 1 := by omega
      have hHalt : Step writeFrameHeader moved (contextHeaderFinish savedInput beforeOutput tail copied blanks) := by
        cases hPad : blanks - copied.length <;>
          simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
            contextHeaderState, contextHeaderFinish, Instruction.next, contextSegment,
            Tape.write, Tape.moveRight, hSub, hPad, List.replicate_succ]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hMove) hHalt
  | cons bit rest ih =>
      have run := (contextHeader_bit savedInput beforeOutput tail copied rest bit blanks).trans (ih (copied ++ [bit]))
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run


/-- Input/output layout for the existing framing routine, with a reserved
input separator, arbitrary saved caller data, and arbitrary cells after the
payload. The routine writes the entire frame after the output prefix. -/
def writeFrameContextStart (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { inputTape := contextSegment (none :: savedInput) bits tail,
    outputTape := { left := beforeOutput } }

def writeFrameContextFinish (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { pc := 23,
    inputTape := { left := bits.reverse.map some ++ none :: savedInput, right := tail },
    outputTape := { left := (frame bits).reverse.map some ++ beforeOutput },
    halted := true }

theorem writeFrameContextStart_layout (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) :
    writeFrameContextStart savedInput beforeOutput tail bits =
      ({ inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
          left := none :: savedInput },
         outputTape := { left := beforeOutput } } : Configuration) := rfl

/-- Framing on an already used output tape, with explicit finite blank
padding beyond the destination head. All earlier caller cells are retained. -/
def writeFrameContextPaddedStart (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := contextSegment (none :: savedInput) bits tail,
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def writeFrameContextPaddedFinish (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 23,
    inputTape := { left := bits.reverse.map some ++ none :: savedInput, right := tail },
    outputTape := {
      left := (frame bits).reverse.map some ++ beforeOutput
      right := List.replicate (blanks - (2 * bits.length + 1)) none },
    halted := true }

theorem writeFrameContextPaddedStart_layout (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    writeFrameContextPaddedStart savedInput beforeOutput tail bits blanks =
      ({ inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
          left := none :: savedInput },
         outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration) := rfl

/-- Same twenty-four native instructions and same exact transition count
as standalone framing. Saved cells beyond either separator are preserved;
there is no implicit tape reset or one-step list copy. -/
theorem writeFrameContextPadded_runs (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor writeFrame (writeFrameContextPaddedStart savedInput beforeOutput tail bits blanks)
      (writeFrameContextPaddedFinish savedInput beforeOutput tail bits blanks) (writeFrameSteps bits) := by
  have hHeader := (contextHeader_loop savedInput beforeOutput tail [] bits blanks).withSubroutine_halted_of_closed
    [] writeFrameHeader
    (rewindBitstring.asSubroutine 9 14 ++ copyBitstring.asSubroutine 14 23 ++ [.halt]) 9
    (by change 0 < 8; decide) rfl rfl writeFrameHeader_control_closed
  change RunsFor writeFrame (writeFrameContextPaddedStart savedInput beforeOutput tail bits blanks)
    ((contextHeaderFinish savedInput beforeOutput tail bits blanks).resumeAt 9)
    (5 * bits.length + 4) at hHeader
  let output : Tape := {
    left := some false :: List.replicate bits.length (some true) ++ beforeOutput
    right := List.replicate (blanks - (bits.length + 1)) none }
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := savedInput, right := bits.map some ++ none :: tail } : Tape).moveRight,
      outputTape := output, halted := true }
  have hRewind := (rewindScratch_runs_from savedInput bits none tail output).withSubroutine_halted_of_closed
    (writeFrameHeader.asSubroutine 0 9) rewindBitstring
    (copyBitstring.asSubroutine 14 23 ++ [.halt]) 14
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor writeFrame ((contextHeaderFinish savedInput beforeOutput tail bits blanks).resumeAt 9)
    (rewound.resumeAt 14) (2 * bits.length + 4) at hRewind
  have hCopyStart : rewound.resumeAt 14 =
      (copySegmentStart (none :: savedInput) output.left tail bits (blanks - (bits.length + 1))).rebasePc 14 := by
    cases bits <;> simp [rewound, copySegmentStart_layout, Configuration.resumeAt,
      Configuration.rebasePc, output, Tape.moveRight]
  rw [hCopyStart] at hRewind
  have hCopy := (copySegment_runs (none :: savedInput) output.left tail bits (blanks - (bits.length + 1))).withSubroutine_halted_of_closed
    (writeFrameHeader.asSubroutine 0 9 ++ rewindBitstring.asSubroutine 9 14)
    copyBitstring [.halt] 23
    (by change 0 < 8; decide) rfl rfl copyBitstring_control_closed
  change RunsFor writeFrame
    ((copySegmentStart (none :: savedInput) output.left tail bits (blanks - (bits.length + 1))).rebasePc 14)
    ((copySegmentFinish (none :: savedInput) output.left tail bits (blanks - (bits.length + 1))).resumeAt 23)
    (copyBitstringSteps bits) at hCopy
  have hFinish : copySegmentFinish (none :: savedInput) output.left tail bits (blanks - (bits.length + 1)) =
      { writeFrameContextPaddedFinish savedInput beforeOutput tail bits blanks with pc := 7 } := by
    simp [copySegmentFinish, writeFrameContextPaddedFinish, output, frame, List.reverse_append,
      List.map_append, List.append_assoc, List.reverse_replicate]
    omega
  rw [hFinish] at hCopy
  have hHalt : Step writeFrame
      ((writeFrameContextPaddedFinish savedInput beforeOutput tail bits blanks).resumeAt 23)
      (writeFrameContextPaddedFinish savedInput beforeOutput tail bits blanks) := by
    simp [Step, successors, next, writeFrame, writeFrameHeader, rewindBitstring,
      copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
      writeFrameContextPaddedFinish, Configuration.resumeAt, Instruction.next]
  simpa only [writeFrameSteps, Configuration.resumeAt] using
    RunsFor.succ ((hHeader.trans hRewind).trans hCopy) hHalt

theorem writeFrameContext_runs (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) :
    RunsFor writeFrame (writeFrameContextStart savedInput beforeOutput tail bits)
      (writeFrameContextFinish savedInput beforeOutput tail bits) (writeFrameSteps bits) := by
  simpa [writeFrameContextPaddedStart, writeFrameContextPaddedFinish,
    writeFrameContextStart, writeFrameContextFinish] using
    writeFrameContextPadded_runs savedInput beforeOutput tail bits 0

theorem writeFrameContext_eval (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) :
    evalConfigWithin writeFrame (writeFrameContextStart savedInput beforeOutput tail bits)
      (writeFrameSteps bits) =
      PMF.pure (writeFrameContextFinish savedInput beforeOutput tail bits) :=
  (writeFrameContext_runs savedInput beforeOutput tail bits).evalConfigWithin_eq_pure_of_no_randomBit
    writeFrame_no_randomBit

/-- On any finite input tape, the actual count/rewind/copy passes stop
with the input head on a blank and the output head at a fresh blank
frontier. A rewind may also expose earlier bits before the nearest saved
separator; those cells are copied by real transitions, not discarded.
This assertion is about stopping and physical layout, not frame validity. -/
theorem writeFrame_terminates_with_layout (input : Tape)
    (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 100 * (input.cells +
        ({ left := beforeOutput, right := List.replicate blanks none } : Tape).cells) + 100 ∧
      RunsFor writeFrame
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  obtain ⟨header, headerTime, headerSaved, headerBlanks,
    hHeaderTime, hHeaderRun, hHeaderHalt, hHeaderBlank, hHeaderOutput⟩ :=
    writeFrameHeader_terminates_with_layout input beforeOutput blanks
  obtain ⟨rewound, leading, savedInput, hLength, hRewindRun, hRewindHalt,
    hRewindInput, hRewindOutput⟩ :=
    rewindBitstring_terminates_with_layout header.inputTape header.outputTape
  let copyStart := copySegmentStart (none :: savedInput) headerSaved header.inputTape.right leading headerBlanks
  let copied := copySegmentFinish (none :: savedInput) headerSaved header.inputTape.right leading headerBlanks
  let finish : Configuration := { copied with pc := 23 }
  have hCopyEntry : rewound.resumeAt 14 = copyStart.rebasePc 14 := by
    dsimp only [copyStart]
    rw [copySegmentStart_layout]
    simp only [Configuration.resumeAt, Configuration.rebasePc, hRewindInput,
      hRewindOutput, hHeaderBlank, hHeaderOutput, List.singleton_append]
  let a := writeFrameHeader.asSubroutine 0 9
  let b := rewindBitstring.asSubroutine 9 14
  let k := copyBitstring.asSubroutine 14 23
  have hHeader := hHeaderRun.withSubroutine_halted_of_closed
    [] writeFrameHeader (b ++ k ++ [.halt]) 9
    (by change 0 < 8; decide) rfl hHeaderHalt writeFrameHeader_control_closed
  change RunsFor writeFrame
    ({ inputTape := input, outputTape := output } : Configuration) (header.resumeAt 9) headerTime at hHeader
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    a rewindBitstring (k ++ [.halt]) 14
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor writeFrame (header.resumeAt 9) (rewound.resumeAt 14) (2 * leading.length + 4) at hRewind
  have hCopy := (copySegment_runs (none :: savedInput) headerSaved header.inputTape.right leading headerBlanks).withSubroutine_halted_of_closed
    (a ++ b) copyBitstring [.halt] 23
      (by change 0 < 8; decide) rfl rfl copyBitstring_control_closed
  change RunsFor writeFrame (copyStart.rebasePc 14) (copied.resumeAt 23) (copyBitstringSteps leading) at hCopy
  rw [← hCopyEntry] at hCopy
  have hHalt : Step writeFrame (copied.resumeAt 23) finish := by
    simp [Step, successors, next, writeFrame, writeFrameHeader, rewindBitstring,
      copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
      copied, finish, copySegmentFinish, Configuration.resumeAt, Instruction.next]
  refine ⟨finish, headerTime + (2 * leading.length + 4) + copyBitstringSteps leading + 1,
    leading.reverse.map some ++ headerSaved, headerBlanks - leading.length,
    ?_, RunsFor.succ ((hHeader.trans hRewind).trans hCopy) hHalt, rfl, rfl, rfl⟩
  have hCopyTime := copyBitstringSteps_le leading
  have hStorage := sourceStorage_le_of_run hHeaderRun
  have hLeft : header.inputTape.left.length ≤ header.inputTape.cells := by
    dsimp only [Tape.cells]
    omega
  dsimp only [sourceStorage] at hStorage
  change header.inputTape.cells + header.outputTape.cells ≤ input.cells + output.cells + headerTime at hStorage
  change _ ≤ 100 * (input.cells + output.cells) + 100
  omega

end Machine
