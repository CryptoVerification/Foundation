import Foundation.Crypto.Semantics.Machine.GuardedOutput
import Foundation.Crypto.Semantics.Machine.Adversary
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine

open GuardedCompiler

/-- Scan a contiguous bitstring and physically write its unary length and
false terminator. The scanned input cells stay on the input tape, so the
caller can rewind and copy the payload afterwards. -/
def writeFrameHeader : Program :=
  [.branch .input 5 1 1,
   .write .output true, .moveRight .input, .moveRight .output, .jump 0,
   .write .output false, .moveRight .output, .halt]

private def frameHeaderState (copied remaining : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := copied.reverse.map some },
    outputTape := { left := List.replicate copied.length (some true) } }

def writeFrameHeaderFinish (bits : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { left := bits.reverse.map some },
    outputTape := { left := some false :: List.replicate bits.length (some true) },
    halted := true }

private theorem frameHeader_bit (copied rest : List Bool) (bit : Bool) :
    RunsFor writeFrameHeader (frameHeaderState copied (bit :: rest))
      (frameHeaderState (copied ++ [bit]) rest) 5 := by
  let start := frameHeaderState copied (bit :: rest)
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration :=
    { selected with pc := 2, outputTape := selected.outputTape.write (some true) }
  let movedInput : Configuration :=
    { written with pc := 3, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hSelect : Step writeFrameHeader start selected := by
    cases bit <;> simp [Step, successors, next, writeFrameHeader, start, selected,
      frameHeaderState, Tape.ofBits, Instruction.next, Configuration.tape]
  have hWrite : Step writeFrameHeader selected written := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written,
      frameHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step writeFrameHeader written movedInput := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, movedInput,
      frameHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step writeFrameHeader movedInput movedOutput := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, movedInput,
      movedOutput, frameHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step writeFrameHeader movedOutput
      (frameHeaderState (copied ++ [bit]) rest) := by
    cases rest <;> simp [Step, successors, next, writeFrameHeader, start, selected, written,
      movedInput, movedOutput, frameHeaderState, Instruction.next, Tape.ofBits, Tape.moveRight,
      Tape.write, List.reverse_append, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hInput) hOutput) hBack

private theorem frameHeader_loop (copied remaining : List Bool) :
    RunsFor writeFrameHeader (frameHeaderState copied remaining)
      (writeFrameHeaderFinish (copied ++ remaining)) (5 * remaining.length + 4) := by
  induction remaining generalizing copied with
  | nil =>
      let start := frameHeaderState copied []
      let selected : Configuration := { start with pc := 5 }
      let written : Configuration :=
        { selected with pc := 6, outputTape := selected.outputTape.write (some false) }
      let moved : Configuration :=
        { written with pc := 7, outputTape := written.outputTape.moveRight }
      have hSelect : Step writeFrameHeader start selected := by
        simp [Step, successors, next, writeFrameHeader, start, selected,
          frameHeaderState, Tape.ofBits, Instruction.next, Configuration.tape]
      have hWrite : Step writeFrameHeader selected written := by
        simp [Step, successors, next, writeFrameHeader, start, selected, written,
          frameHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hMove : Step writeFrameHeader written moved := by
        simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
          frameHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hHalt : Step writeFrameHeader moved (writeFrameHeaderFinish copied) := by
        simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
          frameHeaderState, writeFrameHeaderFinish, Instruction.next, Tape.ofBits,
          Tape.write, Tape.moveRight]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hMove) hHalt
  | cons bit rest ih =>
      have run := (frameHeader_bit copied rest bit).trans (ih (copied ++ [bit]))
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run

theorem writeFrameHeader_runs (bits : List Bool) :
    RunsFor writeFrameHeader (Configuration.initial bits)
      (writeFrameHeaderFinish bits) (5 * bits.length + 4) := by
  have hStart : frameHeaderState [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  simpa [hStart] using frameHeader_loop [] bits

theorem writeFrameHeader_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ writeFrameHeader := by simp [writeFrameHeader]

theorem writeFrameHeader_control_closed (c d : Configuration)
    (hPc : c.pc < writeFrameHeader.length) (step : Step writeFrameHeader c d)
    (_hRunning : d.halted = false) : d.pc < writeFrameHeader.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 8 at hPc
  change d.pc < 8
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, writeFrameHeader,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem frameHeader_blank_run (input output : Tape) (hBlank : input.current = none) :
    RunsFor writeFrameHeader ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 7, inputTape := input, outputTape := (output.write (some false)).moveRight,
         halted := true } : Configuration) 4 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := 5 }
  let written : Configuration := { selected with pc := 6, outputTape := output.write (some false) }
  let moved : Configuration := { written with pc := 7, outputTape := written.outputTape.moveRight }
  have h0 : Step writeFrameHeader start selected := by
    simp [Step, successors, next, writeFrameHeader, start, selected, Instruction.next, Configuration.tape, hBlank]
  have h1 : Step writeFrameHeader selected written := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step writeFrameHeader written moved := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step writeFrameHeader moved { moved with halted := true } := by
    simp [Step, successors, next, writeFrameHeader, moved, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3

private theorem frameHeader_cell_run (input output : Tape) (bit : Bool)
    (hBit : input.current = some bit) :
    RunsFor writeFrameHeader ({ inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) 5 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration := { selected with pc := 2, outputTape := output.write (some true) }
  let moved : Configuration := { written with pc := 3, inputTape := input.moveRight }
  let advanced : Configuration := { moved with pc := 4, outputTape := written.outputTape.moveRight }
  have h0 : Step writeFrameHeader start selected := by
    cases bit <;> simp [Step, successors, next, writeFrameHeader, start, selected,
      Instruction.next, Configuration.tape, hBit]
  have h1 : Step writeFrameHeader selected written := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step writeFrameHeader written moved := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step writeFrameHeader moved advanced := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, moved, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step writeFrameHeader advanced
      ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) := by
    simp [Step, successors, next, writeFrameHeader, start, selected, written, moved, advanced, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem frameHeader_finite_layout (left right : List (Option Bool)) (current : Option Bool)
    (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 5 * (right.length + 1) + 4 ∧
      RunsFor writeFrameHeader
        ({ inputTape := { left := left, current := current, right := right },
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } := by
  induction right generalizing left current beforeOutput blanks with
  | nil =>
      cases current with
      | none =>
          refine ⟨_, 4, some false :: beforeOutput, blanks - 1, by simp,
            frameHeader_blank_run _ _ rfl, rfl, rfl, ?_⟩
          cases blanks <;> simp [Tape.write, Tape.moveRight, List.replicate_succ]
      | some bit =>
          let input : Tape := { left := left, current := some bit }
          let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
          have hBit := frameHeader_cell_run input output bit rfl
          have hBlank := frameHeader_blank_run input.moveRight (output.write (some true)).moveRight rfl
          refine ⟨_, 9, some false :: some true :: beforeOutput, (blanks - 1) - 1,
            by decide, hBit.trans hBlank, rfl, rfl, ?_⟩
          cases blanks with
          | zero => rfl
          | succ blanks => cases blanks <;> simp [output, Tape.write, Tape.moveRight, List.replicate_succ]
  | cons cell rest ih =>
      cases current with
      | none =>
          refine ⟨_, 4, some false :: beforeOutput, blanks - 1, by simp,
            frameHeader_blank_run _ _ rfl, rfl, rfl, ?_⟩
          cases blanks <;> simp [Tape.write, Tape.moveRight, List.replicate_succ]
      | some bit =>
          let input : Tape := { left := left, current := some bit, right := cell :: rest }
          let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
          obtain ⟨finish, used, saved, remaining, hBound, hRun, hHalted, hInput, hOutput⟩ :=
            ih (some bit :: left) cell (some true :: beforeOutput) (blanks - 1)
          have hBit := frameHeader_cell_run input output bit rfl
          have hAdvanced : (output.write (some true)).moveRight =
              ({ left := some true :: beforeOutput, right := List.replicate (blanks - 1) none } : Tape) := by
            cases blanks <;> simp [output, Tape.write, Tape.moveRight, List.replicate_succ]
          rw [← hAdvanced] at hRun
          change RunsFor writeFrameHeader
            ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration)
            finish used at hRun
          exact ⟨finish, 5 + used, saved, remaining, by simp only [List.length_cons]; omega,
            hBit.trans hRun, hHalted, hInput, hOutput⟩

/-- Header generation stops at the first blank of any finite input tape.
The fresh output frontier is retained even when either saved prefix has
internal blanks. No well-formed frame or caller request is assumed. -/
theorem writeFrameHeader_terminates_with_layout (input : Tape)
    (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 5 * input.cells + 4 ∧
      RunsFor writeFrameHeader
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } := by
  obtain ⟨finish, used, saved, remaining, hBound, hRun, hHalted, hInput, hOutput⟩ :=
    frameHeader_finite_layout input.left input.right input.current beforeOutput blanks
  refine ⟨finish, used, saved, remaining, ?_, hRun, hHalted, hInput, hOutput⟩
  dsimp only [Tape.cells]
  omega

private theorem frameHeader_finite_cells (left right : List (Option Bool))
    (current : Option Bool) (output : Tape) :
    ∃ finish used, used ≤ 5 * (right.length + 1) + 4 ∧
      RunsFor writeFrameHeader
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none := by
  induction right generalizing left current output with
  | nil =>
      cases current with
      | none => exact ⟨_, 4, by decide, frameHeader_blank_run _ _ rfl, rfl, rfl⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit }
          have hBit := frameHeader_cell_run input output bit rfl
          have hBlank := frameHeader_blank_run input.moveRight (output.write (some true)).moveRight rfl
          exact ⟨_, 9, by decide, hBit.trans hBlank, rfl, rfl⟩
  | cons cell rest ih =>
      cases current with
      | none => exact ⟨_, 4, by simp, frameHeader_blank_run _ _ rfl, rfl, rfl⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit, right := cell :: rest }
          have hBit := frameHeader_cell_run input output bit rfl
          obtain ⟨finish, used, hBound, hRun, hHalt, hBlank⟩ :=
            ih (some bit :: left) cell (output.write (some true)).moveRight
          change RunsFor writeFrameHeader
            ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration)
            finish used at hRun
          exact ⟨finish, 5 + used, by simp only [List.length_cons]; omega,
            hBit.trans hRun, hHalt, hBlank⟩

/-- Native header generation stops even if the output region is dirty.
Only the input scan determines its time. No valid serialization or saved
output preservation is asserted for such arbitrary caller tapes. -/
theorem writeFrameHeader_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 5 * input.cells + 4 ∧
      RunsFor writeFrameHeader
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.inputTape.current = none := by
  obtain ⟨finish, used, hBound, hRun, hHalt, hBlank⟩ :=
    frameHeader_finite_cells input.left input.right input.current output
  refine ⟨finish, used, ?_, hRun, hHalt, hBlank⟩
  dsimp only [Tape.cells]
  omega

/-- A native implementation of `Machine.frame`: count, write the delimiter,
rewind the unchanged input with real head moves, copy the payload, and halt.
The subroutine calls are finite relocated code, not new machine operations. -/
def writeFrame : Program :=
  writeFrameHeader.asSubroutine 0 9 ++
    rewindBitstring.asSubroutine 9 14 ++
    copyBitstring.asSubroutine 14 23 ++ [.halt]

def writeFrameSteps (bits : List Bool) : Nat :=
  (5 * bits.length + 4) + (2 * bits.length + 4) + copyBitstringSteps bits + 1

def writeFrameFinish (bits : List Bool) : Configuration :=
  { copyScratchFinish [none]
      (some false :: List.replicate bits.length (some true)) bits 0 with pc := 23 }

/-- Full native trace of the framing wrapper. Stored outer blank cells from
the rewind survive; they are not silently removed by a tape reset. -/
theorem writeFrame_runs (bits : List Bool) :
    RunsFor writeFrame (Configuration.initial bits)
      (writeFrameFinish bits) (writeFrameSteps bits) := by
  have header := (writeFrameHeader_runs bits).withSubroutine_halted_of_closed
    [] writeFrameHeader
    (rewindBitstring.asSubroutine 9 14 ++ copyBitstring.asSubroutine 14 23 ++ [.halt]) 9
    (by simp [Configuration.initial, writeFrameHeader]) rfl rfl writeFrameHeader_control_closed
  change RunsFor writeFrame (Configuration.initial bits)
    ((writeFrameHeaderFinish bits).resumeAt 9) (5 * bits.length + 4) at header
  let output : Tape := { left := some false :: List.replicate bits.length (some true) }
  have rewind := (rewindBitstring_runs bits output).withSubroutine_halted_of_closed
    (writeFrameHeader.asSubroutine 0 9) rewindBitstring
    (copyBitstring.asSubroutine 14 23 ++ [.halt]) 14
    (by simp [rewindBitstringStart, rewindBitstring]) rfl rfl rewindBitstring_control_closed
  have hRewindProgram :
      Program.withSubroutine (writeFrameHeader.asSubroutine 0 9) rewindBitstring
        (copyBitstring.asSubroutine 14 23 ++ [.halt]) 14 = writeFrame := by
    simp [Program.withSubroutine, Program.asSubroutine_length, writeFrame,
      writeFrameHeader, List.append_assoc]
  rw [hRewindProgram] at rewind
  change RunsFor writeFrame ((writeFrameHeaderFinish bits).resumeAt 9)
    ((rewindBitstringFinish bits output).resumeAt 14) (2 * bits.length + 4) at rewind
  have copy := (copyScratch_runs [none] output.left bits 0).withSubroutine_halted_of_closed
    (writeFrameHeader.asSubroutine 0 9 ++ rewindBitstring.asSubroutine 9 14)
    copyBitstring [.halt] 23
    (by change 0 < 8; decide) rfl rfl copyBitstring_control_closed
  have hCopyProgram :
      Program.withSubroutine
        (writeFrameHeader.asSubroutine 0 9 ++ rewindBitstring.asSubroutine 9 14)
        copyBitstring [.halt] 23 = writeFrame := by
    simp [Program.withSubroutine, Program.asSubroutine_length, writeFrame,
      writeFrameHeader, rewindBitstring, List.append_assoc]
  rw [hCopyProgram] at copy
  have hCopyStart :
      (copyScratchStart [none] output.left bits 0).rebasePc
        (writeFrameHeader.asSubroutine 0 9 ++ rewindBitstring.asSubroutine 9 14).length =
      (rewindBitstringFinish bits output).resumeAt 14 := by
    change ({
      pc := 14,
      inputTape := { packedLogicalInput bits with left := [none] },
      outputTape := output } : Configuration) =
      ({
        pc := 14,
        inputTape := ({ right := bits.map some ++ [none] } : Tape).moveRight,
        outputTape := output } : Configuration)
    cases bits <;> simp [packedLogicalInput, rewoundTape, Tape.moveRight]
  rw [hCopyStart] at copy
  change RunsFor writeFrame ((rewindBitstringFinish bits output).resumeAt 14)
    ((writeFrameFinish bits).resumeAt 23) (copyBitstringSteps bits) at copy
  have hHalt : Step writeFrame ((writeFrameFinish bits).resumeAt 23) (writeFrameFinish bits) := by
    simp [Step, successors, next, writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, writeFrameFinish, copyScratchFinish,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((header.trans rewind).trans copy) hHalt

theorem writeFrame_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ writeFrame := by
  simp [writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem writeFrameSteps_le (bits : List Bool) :
    writeFrameSteps bits ≤ 13 * bits.length + 11 := by
  have hCopy := copyBitstringSteps_le bits
  simp only [writeFrameSteps]
  omega

theorem writeFrameFinish_outputBits (bits : List Bool) :
    (writeFrameFinish bits).outputBits = frame bits := by
  simp [writeFrameFinish, copyScratchFinish, Configuration.outputBits, Tape.bits,
    frame, List.filterMap_append]

theorem writeFrame_eval (bits : List Bool) :
    evalConfigWithin writeFrame (Configuration.initial bits) (writeFrameSteps bits) =
      PMF.pure (writeFrameFinish bits) :=
  (writeFrame_runs bits).evalConfigWithin_eq_pure_of_no_randomBit writeFrame_no_randomBit

theorem writeFrame_control_closed (c d : Configuration)
    (hPc : c.pc < writeFrame.length) (step : Step writeFrame c d)
    (_hRunning : d.halted = false) : d.pc < writeFrame.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 24 at hPc
  change d.pc < 24
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, writeFrame,
    writeFrameHeader, rewindBitstring, copyBitstring, Program.asSubroutine,
    Instruction.asSubroutine, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Complete native framing has linear stopping overhead on arbitrary
finite tapes. In particular scratch left by malformed caller data need not
be fresh for this runtime statement. Header generation, input rewind,
payload copying and the final caller halt are actual charged transitions. -/
theorem writeFrame_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 200 * (input.cells + output.cells) + 200 ∧
      RunsFor writeFrame ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨header, t₁, h₁, run₁, halt₁, _blank⟩ := writeFrameHeader_terminates_from_anyTape input output
  obtain ⟨rewound, t₂, h₂, run₂, halt₂, _output⟩ :=
    rewindBitstring_terminates_from header.inputTape header.outputTape
  obtain ⟨copied, t₃, h₃, run₃, halt₃⟩ :=
    copyBitstring_terminates_from_anyTape rewound.inputTape rewound.outputTape
  let a := writeFrameHeader.asSubroutine 0 9
  let b := rewindBitstring.asSubroutine 9 14
  let k := copyBitstring.asSubroutine 14 23
  have headerRun := run₁.withSubroutine_halted_of_closed
    [] writeFrameHeader (b ++ k ++ [.halt]) 9
    (by change 0 < 8; decide) rfl halt₁ writeFrameHeader_control_closed
  change RunsFor writeFrame
    ({ inputTape := input, outputTape := output } : Configuration) (header.resumeAt 9) t₁ at headerRun
  have rewindRun := run₂.withSubroutine_halted_of_closed
    a rewindBitstring (k ++ [.halt]) 14
    (by change 0 < 4; decide) rfl halt₂ rewindBitstring_control_closed
  change RunsFor writeFrame (header.resumeAt 9) (rewound.resumeAt 14) t₂ at rewindRun
  have copyRun := run₃.withSubroutine_halted_of_closed
    (a ++ b) copyBitstring [.halt] 23
    (by change 0 < 8; decide) rfl halt₃ copyBitstring_control_closed
  change RunsFor writeFrame (rewound.resumeAt 14) (copied.resumeAt 23) t₃ at copyRun
  let finish : Configuration := { copied with pc := 23, halted := true }
  have last : Step writeFrame (copied.resumeAt 23) finish := by
    simp [Step, successors, next, writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, t₁ + t₂ + t₃ + 1, ?_, RunsFor.succ ((headerRun.trans rewindRun).trans copyRun) last, rfl⟩
  have storage₁ := sourceStorage_le_of_run run₁
  have storage₂ := sourceStorage_le_of_run run₂
  have hLeft : header.inputTape.left.length ≤ header.inputTape.cells := by dsimp only [Tape.cells]; omega
  change header.inputTape.cells + header.outputTape.cells ≤ input.cells + output.cells + t₁ at storage₁
  change rewound.inputTape.cells + rewound.outputTape.cells ≤ header.inputTape.cells + header.outputTape.cells + t₂ at storage₂
  omega

/-- Invoke the entire framing wrapper on the specified initial tapes.
Random instructions elsewhere in the caller do not change its deterministic
return distribution or make its head movements free. -/
theorem writeFrame_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre writeFrame suffix returnPc)
      ((Configuration.initial bits).rebasePc pre.length) (writeFrameSteps bits) =
      PMF.pure ((writeFrameFinish bits).resumeAt returnPc) :=
  (writeFrame_runs bits).evalConfigWithin_withSubroutine_halted_of_closed
    pre writeFrame suffix returnPc (by simp [Configuration.initial, writeFrame,
      writeFrameHeader, rewindBitstring, copyBitstring, Program.asSubroutine_length])
    rfl rfl writeFrame_control_closed writeFrame_no_randomBit

theorem writeFrame_haltsWithin (bits : List Bool) :
    HaltsWithin writeFrame bits (13 * bits.length + 11) := by
  have hHalt : HaltsWith writeFrame bits (frame bits) (writeFrameSteps bits) :=
    ⟨_, writeFrame_runs bits, rfl, writeFrameFinish_outputBits bits⟩
  exact (hHalt.haltsWithin_of_no_randomBit writeFrame_no_randomBit).mono (writeFrameSteps_le bits)

theorem writeFrame_polynomialTime : PolynomialTime writeFrame := by
  refine ⟨fun m => 13 * m + 11, ?_, writeFrame_haltsWithin⟩
  exact ((PolynomiallyBounded.const 13).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 11)

theorem writeFrame_evalWithin (bits : List Bool) :
    evalWithin writeFrame bits (13 * bits.length + 11) = PMF.pure (some (frame bits)) := by
  have hHalt : HaltsWith writeFrame bits (frame bits) (writeFrameSteps bits) :=
    ⟨_, writeFrame_runs bits, rfl, writeFrameFinish_outputBits bits⟩
  rw [evalWithin_eq_of_haltsWithin writeFrame bits (13 * bits.length + 11) (writeFrameSteps bits)
    (writeFrame_haltsWithin bits) (hHalt.haltsWithin_of_no_randomBit writeFrame_no_randomBit)]
  exact hHalt.evalWithin_eq_pure_of_no_randomBit writeFrame_no_randomBit

end Machine
