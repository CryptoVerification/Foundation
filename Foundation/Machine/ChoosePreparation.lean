import Foundation.Machine.DelimitedInput
import Foundation.Machine.ProtocolPrefix

namespace Machine

/-- Count a delimited public-key code by writing one unary header bit per
payload bit. The extra initial true bit accounts for the choose tag. On a
terminated field the routine writes the false header terminator and the
false choose tag. It does not yet copy the key payload: a charged rewind and
`readDelimited` supply that second pass. All reads and writes are one-cell
native instructions, not a free length or framing operation. -/
def writeChooseHeader : Program :=
  [.write .output true, .moveRight .output,
   .branch .input 14 9 3,
   .moveRight .input, .branch .input 14 5 5,
   .write .output true, .moveRight .input, .moveRight .output, .jump 2,
   .moveRight .input, .write .output false, .moveRight .output,
   .write .output false, .halt, .halt]

private def chooseHeaderState (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) : Configuration :=
  { pc := 2,
    inputTape := { Tape.ofBits (FiniteBitEncoding.delimit bits ++ tail) with left := beforeInput },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

/-- Invocation on a canonical delimited element field. Previously saved
public data may precede either head; the caller's output cells are blank
at and to the right of its head, including explicitly stored padding. -/
def writeChooseHeaderStart (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) : Configuration :=
  { chooseHeaderState beforeInput beforeOutput bits tail blanks with pc := 0 }

/-- Exact returned layout. The output head is on the false choose tag;
the next instruction can advance it before copying the element code.
The input head follows the complete delimited field, retaining its cells. -/
def writeChooseHeaderFinish (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) : Configuration :=
  { pc := 13,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit bits).reverse.map some ++ beforeInput },
    outputTape := {
      left := some false :: (List.replicate (bits.length + 1) (some true) ++ beforeOutput)
      current := some false
      right := List.replicate (blanks - (bits.length + 2)) none },
    halted := true }

private def chooseHeaderLoopFinish (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) : Configuration :=
  { pc := 13,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit bits).reverse.map some ++ beforeInput },
    outputTape := {
      left := some false :: (List.replicate bits.length (some true) ++ beforeOutput)
      current := some false
      right := List.replicate (blanks - (bits.length + 1)) none },
    halted := true }

private theorem chooseHeader_one (beforeInput beforeOutput : List (Option Bool))
    (bit : Bool) (bits tail : List Bool) (blanks : Nat) :
    RunsFor writeChooseHeader (chooseHeaderState beforeInput beforeOutput (bit :: bits) tail blanks)
      (chooseHeaderState (some bit :: some true :: beforeInput) (some true :: beforeOutput)
        bits tail (blanks - 1)) 7 := by
  let start := chooseHeaderState beforeInput beforeOutput (bit :: bits) tail blanks
  let selected : Configuration := { start with pc := 3 }
  let payload : Configuration := { selected with pc := 4, inputTape := selected.inputTape.moveRight }
  let ready : Configuration := { payload with pc := 5 }
  let written : Configuration := { ready with pc := 6, outputTape := ready.outputTape.write (some true) }
  let movedInput : Configuration := { written with pc := 7, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 8, outputTape := movedInput.outputTape.moveRight }
  have h0 : Step writeChooseHeader start selected := by
    simp [Step, successors, next, writeChooseHeader, start, selected, chooseHeaderState,
      FiniteBitEncoding.delimit, Tape.ofBits, Instruction.next, Configuration.tape]
  have h1 : Step writeChooseHeader selected payload := by
    simp [Step, successors, next, writeChooseHeader, selected, payload, start,
      chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step writeChooseHeader payload ready := by
    cases bit <;> simp [Step, successors, next, writeChooseHeader, payload, ready, selected, start,
      chooseHeaderState, FiniteBitEncoding.delimit, Tape.ofBits, Tape.moveRight,
      Instruction.next, Configuration.tape]
  have h3 : Step writeChooseHeader ready written := by
    simp [Step, successors, next, writeChooseHeader, ready, written, payload, selected, start,
      chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step writeChooseHeader written movedInput := by
    simp [Step, successors, next, writeChooseHeader, written, movedInput, ready, payload, selected, start,
      chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step writeChooseHeader movedInput movedOutput := by
    simp [Step, successors, next, writeChooseHeader, movedInput, movedOutput, written, ready, payload, selected, start,
      chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h6 : Step writeChooseHeader movedOutput
      (chooseHeaderState (some bit :: some true :: beforeInput) (some true :: beforeOutput)
        bits tail (blanks - 1)) := by
    cases blanks <;> cases bits <;>
      simp [Step, successors, next, writeChooseHeader, movedOutput, movedInput, written, ready,
        payload, selected, start, chooseHeaderState, FiniteBitEncoding.delimit,
        Tape.ofBits, Tape.moveRight, Tape.write, Instruction.next, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6

private theorem chooseHeader_loop (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) :
    RunsFor writeChooseHeader (chooseHeaderState beforeInput beforeOutput bits tail blanks)
      (chooseHeaderLoopFinish beforeInput beforeOutput bits tail blanks) (7 * bits.length + 6) := by
  induction bits generalizing beforeInput beforeOutput blanks with
  | nil =>
      let start := chooseHeaderState beforeInput beforeOutput [] tail blanks
      let selected : Configuration := { start with pc := 9 }
      let movedInput : Configuration := { selected with pc := 10, inputTape := selected.inputTape.moveRight }
      let written : Configuration := { movedInput with pc := 11, outputTape := movedInput.outputTape.write (some false) }
      let movedOutput : Configuration := { written with pc := 12, outputTape := written.outputTape.moveRight }
      let tag : Configuration := { movedOutput with pc := 13, outputTape := movedOutput.outputTape.write (some false) }
      have h0 : Step writeChooseHeader start selected := by
        simp [Step, successors, next, writeChooseHeader, start, selected, chooseHeaderState,
          FiniteBitEncoding.delimit, Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step writeChooseHeader selected movedInput := by
        simp [Step, successors, next, writeChooseHeader, selected, movedInput, start, chooseHeaderState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step writeChooseHeader movedInput written := by
        simp [Step, successors, next, writeChooseHeader, movedInput, written, selected, start, chooseHeaderState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h3 : Step writeChooseHeader written movedOutput := by
        simp [Step, successors, next, writeChooseHeader, written, movedOutput, movedInput, selected, start,
          chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h4 : Step writeChooseHeader movedOutput tag := by
        simp [Step, successors, next, writeChooseHeader, movedOutput, tag, written, movedInput, selected, start,
          chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h5 : Step writeChooseHeader tag (chooseHeaderLoopFinish beforeInput beforeOutput [] tail blanks) := by
        cases tail <;> cases blanks <;>
          simp [Step, successors, next, writeChooseHeader, tag, movedOutput, written, movedInput,
            selected, start, chooseHeaderState, chooseHeaderLoopFinish, FiniteBitEncoding.delimit,
            Tape.ofBits, Tape.moveRight, Tape.write, Instruction.next, List.replicate_succ]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5
  | cons bit bits ih =>
      have run := (chooseHeader_one beforeInput beforeOutput bit bits tail blanks).trans
        (ih (some bit :: some true :: beforeInput) (some true :: beforeOutput) (blanks - 1))
      have hFinish : chooseHeaderLoopFinish (some bit :: some true :: beforeInput)
          (some true :: beforeOutput) bits tail (blanks - 1) =
          chooseHeaderLoopFinish beforeInput beforeOutput (bit :: bits) tail blanks := by
        simp [chooseHeaderLoopFinish, FiniteBitEncoding.delimit, List.reverse_cons,
          List.map_append, List.append_assoc, List.replicate_succ']
        omega
      rw [hFinish] at run
      convert run using 1
      simp only [List.length_cons]
      omega

theorem writeChooseHeader_runs (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) :
    RunsFor writeChooseHeader (writeChooseHeaderStart beforeInput beforeOutput bits tail blanks)
      (writeChooseHeaderFinish beforeInput beforeOutput bits tail blanks) (7 * bits.length + 8) := by
  let start := writeChooseHeaderStart beforeInput beforeOutput bits tail blanks
  let written : Configuration := { start with pc := 1, outputTape := start.outputTape.write (some true) }
  have h0 : Step writeChooseHeader start written := by
    simp [Step, successors, next, writeChooseHeader, start, written, writeChooseHeaderStart,
      chooseHeaderState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step writeChooseHeader written
      (chooseHeaderState beforeInput (some true :: beforeOutput) bits tail (blanks - 1)) := by
    cases blanks <;> simp [Step, successors, next, writeChooseHeader, start, written,
      writeChooseHeaderStart, chooseHeaderState, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.write, List.replicate_succ]
  have run := (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1).trans
    (chooseHeader_loop beforeInput (some true :: beforeOutput) bits tail (blanks - 1))
  have hFinish : chooseHeaderLoopFinish beforeInput (some true :: beforeOutput) bits tail (blanks - 1) =
      writeChooseHeaderFinish beforeInput beforeOutput bits tail blanks := by
    simp [chooseHeaderLoopFinish, writeChooseHeaderFinish, List.replicate_succ', List.append_assoc]
    omega
  rw [hFinish] at run
  convert run using 1
  omega

theorem writeChooseHeader_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ writeChooseHeader := by simp [writeChooseHeader]

theorem writeChooseHeader_eval (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) :
    evalConfigWithin writeChooseHeader (writeChooseHeaderStart beforeInput beforeOutput bits tail blanks)
      (7 * bits.length + 8) = PMF.pure (writeChooseHeaderFinish beforeInput beforeOutput bits tail blanks) :=
  (writeChooseHeader_runs beforeInput beforeOutput bits tail blanks).evalConfigWithin_eq_pure_of_no_randomBit
    writeChooseHeader_no_randomBit

/-- Native counting uses a linear number of transitions in the delimited
current field, including its terminating bit. This bound concerns the
canonical invocation fixture, not a complete two-stage simulator. -/
theorem writeChooseHeader_steps_le (bits tail : List Bool) :
    7 * bits.length + 8 ≤ 4 * (FiniteBitEncoding.delimit bits ++ tail).length + 4 := by
  simp only [List.length_append, FiniteBitEncoding.delimit_length]
  omega

theorem writeChooseHeader_output (beforeInput beforeOutput : List (Option Bool))
    (bits tail : List Bool) (blanks : Nat) :
    (writeChooseHeaderFinish beforeInput beforeOutput bits tail blanks).outputBits =
      beforeOutput.reverse.filterMap id ++ List.replicate (bits.length + 1) true ++ [false, false] := by
  simp [writeChooseHeaderFinish, Configuration.outputBits, Tape.bits,
    List.reverse_append, List.filterMap_append, List.append_assoc]

theorem writeChooseHeader_control_closed (c d : Configuration)
    (hPc : c.pc < writeChooseHeader.length) (step : Step writeChooseHeader c d)
    (_hRunning : d.halted = false) : d.pc < writeChooseHeader.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 15 at hPc
  change d.pc < 15
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, writeChooseHeader,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem moveRight_blank_padding (before : List (Option Bool))
    (current : Option Bool) (blanks : Nat) :
    ({ left := before, current := current, right := List.replicate blanks none } : Tape).moveRight =
      { left := current :: before, right := List.replicate (blanks - 1) none } := by
  cases blanks <;> simp [Tape.moveRight, List.replicate_succ]

/-- Assemble the full framed choose request from a delimited public-key
field. The caller has reserved a blank immediately before that field and
saved the public-input prefix on the output tape. Header counting and field
copying make two native passes; the parser's status bit is then explicitly
erased. No code contains the key, security parameter, or instance family. -/
def assembleChooseField : Program :=
  writeChooseHeader.asSubroutine 0 16 ++ [.moveRight .output] ++
    rewindBitstring.asSubroutine 17 22 ++ readDelimited.asSubroutine 22 39 ++
    [.moveLeft .output, .erase .output, .halt]

def assembleChooseFieldStart (savedInput publicInput : List (Option Bool))
    (key tail : List Bool) (blanks : Nat) : Configuration :=
  writeChooseHeaderStart (none :: savedInput) publicInput key tail blanks

theorem assembleChooseFieldStart_layout (savedInput publicInput : List (Option Bool))
    (key tail : List Bool) (blanks : Nat) :
    assembleChooseFieldStart savedInput publicInput key tail blanks =
      { inputTape := { Tape.ofBits (FiniteBitEncoding.delimit key ++ tail) with
          left := none :: savedInput },
        outputTape := { left := publicInput, right := List.replicate blanks none } } := rfl

def assembleChooseFieldFinish (savedInput publicInput : List (Option Bool))
    (key tail : List Bool) (blanks : Nat) : Configuration :=
  { pc := 41,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit key).reverse.map some ++ none :: savedInput },
    outputTape := {
      left := key.reverse.map some ++ some false :: some false ::
        (List.replicate (key.length + 1) (some true) ++ publicInput)
      right := none :: List.replicate (blanks - (2 * key.length + 4)) none },
    halted := true }

def assembleChooseFieldSteps (key tail : List Bool) : Nat :=
  (7 * key.length + 8) + 1 + (2 * (FiniteBitEncoding.delimit key).length + 4) +
    readDelimitedSteps (FiniteBitEncoding.delimit key ++ tail) + 3

/-- Exact native trace for the public-key field of a DDH triple. A following
field begins with `nextBit`; canonical triple encodings always provide such
a bit because the second element has its own delimiter, even for empty
codes. Saved input and the remainder of the triple are not overwritten. -/
theorem assembleChooseField_runs (savedInput publicInput : List (Option Bool))
    (key : List Bool) (nextBit : Bool) (tail : List Bool) (blanks : Nat) :
    RunsFor assembleChooseField (assembleChooseFieldStart savedInput publicInput key (nextBit :: tail) blanks)
      (assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks)
      (assembleChooseFieldSteps key (nextBit :: tail)) := by
  let a := writeChooseHeader.asSubroutine 0 16
  let b := rewindBitstring.asSubroutine 17 22
  let k := readDelimited.asSubroutine 22 39
  let afterHeader := some false :: some false ::
    (List.replicate (key.length + 1) (some true) ++ publicInput)
  let freshOutput : Tape := { left := afterHeader, right := List.replicate (blanks - (key.length + 3)) none }
  let rewindStart : Configuration :=
    { inputTape := { Tape.ofBits (nextBit :: tail) with
        left := (FiniteBitEncoding.delimit key).reverse.map some ++ none :: savedInput },
      outputTape := freshOutput }
  let rewindFinish : Configuration :=
    { pc := 3,
      inputTape := ({
        left := savedInput
        right := (FiniteBitEncoding.delimit key).map some ++ (nextBit :: tail).map some } : Tape).moveRight,
      outputTape := freshOutput, halted := true }
  have hHeader := (writeChooseHeader_runs (none :: savedInput) publicInput key (nextBit :: tail) blanks).withSubroutine_halted_of_closed
    [] writeChooseHeader ([.moveRight .output] ++ b ++ k ++ [.moveLeft .output, .erase .output, .halt]) 16
    (by change 0 < 15; decide) rfl rfl writeChooseHeader_control_closed
  change RunsFor assembleChooseField
    (assembleChooseFieldStart savedInput publicInput key (nextBit :: tail) blanks)
    ((writeChooseHeaderFinish (none :: savedInput) publicInput key (nextBit :: tail) blanks).resumeAt 16)
    (7 * key.length + 8) at hHeader
  have hPadding : blanks - (key.length + 2) - 1 = blanks - (key.length + 3) := by omega
  have hMove : Step assembleChooseField
      ((writeChooseHeaderFinish (none :: savedInput) publicInput key (nextBit :: tail) blanks).resumeAt 16)
      (rewindStart.rebasePc 17) := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, Configuration.rebasePc,
      writeChooseHeaderFinish, rewindStart, freshOutput, afterHeader,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      moveRight_blank_padding, hPadding]
  have hRewind := (rewindScratch_runs_from savedInput (FiniteBitEncoding.delimit key)
      (some nextBit) (tail.map some) freshOutput).withSubroutine_halted_of_closed
    (a ++ [.moveRight .output]) rewindBitstring (k ++ [.moveLeft .output, .erase .output, .halt]) 22
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor assembleChooseField (rewindStart.rebasePc 17) (rewindFinish.resumeAt 22)
    (2 * (FiniteBitEncoding.delimit key).length + 4) at hRewind
  have hCopyStart : rewindFinish.resumeAt 22 =
      (readDelimitedPaddedStart (none :: savedInput) afterHeader
        (FiniteBitEncoding.delimit key ++ nextBit :: tail) (blanks - (key.length + 3))).rebasePc 22 := by
    cases key <;> simp [rewindFinish, readDelimitedPaddedStart_layout, Configuration.resumeAt,
      Configuration.rebasePc, freshOutput, FiniteBitEncoding.delimit, Tape.ofBits, Tape.moveRight]
  rw [hCopyStart] at hRewind
  have hCopy := (readDelimitedPadded_runs (none :: savedInput) afterHeader
      (FiniteBitEncoding.delimit key ++ nextBit :: tail) (blanks - (key.length + 3))).withSubroutine_halted_of_closed
    (a ++ [.moveRight .output] ++ b) readDelimited [.moveLeft .output, .erase .output, .halt] 39
    (by change 0 < 16; decide) rfl
    (by simp [readDelimitedPaddedFinish]) readDelimited_control_closed
  change RunsFor assembleChooseField
    ((readDelimitedPaddedStart (none :: savedInput) afterHeader
      (FiniteBitEncoding.delimit key ++ nextBit :: tail) (blanks - (key.length + 3))).rebasePc 22)
    ((readDelimitedPaddedFinish (none :: savedInput) afterHeader
      (FiniteBitEncoding.delimit key ++ nextBit :: tail) (blanks - (key.length + 3))).resumeAt 39)
    (readDelimitedSteps (FiniteBitEncoding.delimit key ++ nextBit :: tail)) at hCopy
  let beforeErase : Configuration :=
    { assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks with
      pc := 40, outputTape := (assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks).outputTape.write (some true),
      halted := false }
  let erased : Configuration :=
    { assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks with halted := false }
  have hSubtract : blanks - (key.length + 3) - (key.length + 1) = blanks - (2 * key.length + 4) := by omega
  have hBack : Step assembleChooseField
      ((readDelimitedPaddedFinish (none :: savedInput) afterHeader
        (FiniteBitEncoding.delimit key ++ nextBit :: tail) (blanks - (key.length + 3))).resumeAt 39) beforeErase := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring, readDelimited,
      Program.asSubroutine, Instruction.asSubroutine, readDelimitedPaddedFinish,
      scanDelimited_complete, Configuration.resumeAt, beforeErase, assembleChooseFieldFinish,
      afterHeader, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Tape.write, hSubtract]
  have hErase : Step assembleChooseField beforeErase erased := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring, readDelimited,
      Program.asSubroutine, Instruction.asSubroutine, beforeErase, erased, assembleChooseFieldFinish,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write]
  have hHalt : Step assembleChooseField erased
      (assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks) := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring, readDelimited,
      Program.asSubroutine, Instruction.asSubroutine, erased, assembleChooseFieldFinish, Instruction.next]
  simpa only [assembleChooseFieldSteps, Nat.add_assoc] using
    RunsFor.succ (RunsFor.succ (RunsFor.succ
      (((RunsFor.succ hHeader hMove).trans hRewind).trans hCopy) hBack) hErase) hHalt

theorem assembleChooseField_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ assembleChooseField := by
  simp [assembleChooseField, writeChooseHeader, rewindBitstring, readDelimited,
    Program.asSubroutine, Instruction.asSubroutine]

theorem assembleChooseField_eval (savedInput publicInput : List (Option Bool))
    (key : List Bool) (nextBit : Bool) (tail : List Bool) (blanks : Nat) :
    evalConfigWithin assembleChooseField
      (assembleChooseFieldStart savedInput publicInput key (nextBit :: tail) blanks)
      (assembleChooseFieldSteps key (nextBit :: tail)) =
      PMF.pure (assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks) :=
  (assembleChooseField_runs savedInput publicInput key nextBit tail blanks).evalConfigWithin_eq_pure_of_no_randomBit
    assembleChooseField_no_randomBit

/-- The original finite public prefix is followed by precisely the existing
framed choose request, with no parser status bit or counter cells leaking
into the output. This observation is justified by the native trace above. -/
theorem assembleChooseField_output (savedInput publicInput : List (Option Bool))
    (key tail : List Bool) (blanks : Nat) :
    (assembleChooseFieldFinish savedInput publicInput key tail blanks).outputBits =
      publicInput.reverse.filterMap id ++ frame (false :: key) := by
  simp [assembleChooseFieldFinish, Configuration.outputBits, Tape.bits, frame,
    List.reverse_append, List.filterMap_append, List.append_assoc]

theorem assembleChooseFieldSteps_le (key tail : List Bool) :
    assembleChooseFieldSteps key tail ≤ 10 * (FiniteBitEncoding.delimit key ++ tail).length + 30 := by
  have hReader := readDelimitedSteps_le (FiniteBitEncoding.delimit key ++ tail)
  simp only [assembleChooseFieldSteps, List.length_append, FiniteBitEncoding.delimit_length] at *
  omega

theorem assembleChooseField_haltsFrom (savedInput publicInput : List (Option Bool))
    (key : List Bool) (nextBit : Bool) (tail : List Bool) (blanks : Nat)
    (finish : Configuration)
    (run : PaddedRunsFor assembleChooseField
      (assembleChooseFieldStart savedInput publicInput key (nextBit :: tail) blanks)
      finish (assembleChooseFieldSteps key (nextBit :: tail))) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [assembleChooseField_eval] at hMem
  have hEq : finish = assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) blanks := by
    simpa using hMem
  rw [hEq]
  rfl

theorem assembleChooseField_control_closed (c d : Configuration)
    (hPc : c.pc < assembleChooseField.length) (step : Step assembleChooseField c d)
    (_hRunning : d.halted = false) : d.pc < assembleChooseField.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 42 at hPc
  change d.pc < 42
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, assembleChooseField,
    writeChooseHeader, rewindBitstring, readDelimited, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem chooseHeader_blank_from_anyTape (input output : Tape)
    (hBlank : input.current = none) :
    RunsFor writeChooseHeader
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have h0 : Step writeChooseHeader
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next, Configuration.tape, hBlank]
  have h1 : Step writeChooseHeader
      ({ pc := 14, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem chooseHeader_false_from_anyTape (input output : Tape)
    (hFalse : input.current = some false) :
    ∃ finish, RunsFor writeChooseHeader
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      finish 6 ∧ finish.halted = true := by
  let start : Configuration := { pc := 2, inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := 9 }
  let moved : Configuration := { selected with pc := 10, inputTape := input.moveRight }
  let written : Configuration := { moved with pc := 11, outputTape := output.write (some false) }
  let advanced : Configuration := { written with pc := 12, outputTape := written.outputTape.moveRight }
  let tag : Configuration := { advanced with pc := 13, outputTape := advanced.outputTape.write (some false) }
  have h0 : Step writeChooseHeader start selected := by
    simp [Step, successors, next, writeChooseHeader, start, selected, Instruction.next,
      Configuration.tape, hFalse]
  have h1 : Step writeChooseHeader selected moved := by
    simp [Step, successors, next, writeChooseHeader, start, selected, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h2 : Step writeChooseHeader moved written := by
    simp [Step, successors, next, writeChooseHeader, start, selected, moved, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h3 : Step writeChooseHeader written advanced := by
    simp [Step, successors, next, writeChooseHeader, start, selected, moved, written, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step writeChooseHeader advanced tag := by
    simp [Step, successors, next, writeChooseHeader, start, selected, moved, written, advanced, tag,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step writeChooseHeader tag { tag with halted := true } := by
    simp [Step, successors, next, writeChooseHeader, start, selected, moved, written, advanced, tag,
      Instruction.next]
  exact ⟨_, RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5, rfl⟩

private theorem chooseHeader_true_prefix_from_anyTape (input output : Tape)
    (hTrue : input.current = some true) :
    RunsFor writeChooseHeader
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 4, inputTape := input.moveRight, outputTape := output } : Configuration) 2 := by
  have h0 : Step writeChooseHeader
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 3, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next, Configuration.tape, hTrue]
  have h1 : Step writeChooseHeader
      ({ pc := 3, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 4, inputTape := input.moveRight, outputTape := output } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem chooseHeader_payload_from_anyTape (input output : Tape) (bit : Bool)
    (hBit : input.current = some bit) :
    RunsFor writeChooseHeader
      ({ pc := 4, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 2, inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) 5 := by
  let start : Configuration := { pc := 4, inputTape := input, outputTape := output }
  let ready : Configuration := { start with pc := 5 }
  let written : Configuration := { ready with pc := 6, outputTape := output.write (some true) }
  let moved : Configuration := { written with pc := 7, inputTape := input.moveRight }
  let advanced : Configuration := { moved with pc := 8, outputTape := written.outputTape.moveRight }
  have h0 : Step writeChooseHeader start ready := by
    cases bit <;> simp [Step, successors, next, writeChooseHeader, start, ready,
      Instruction.next, Configuration.tape, hBit]
  have h1 : Step writeChooseHeader ready written := by
    simp [Step, successors, next, writeChooseHeader, start, ready, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step writeChooseHeader written moved := by
    simp [Step, successors, next, writeChooseHeader, start, ready, written, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step writeChooseHeader moved advanced := by
    simp [Step, successors, next, writeChooseHeader, start, ready, written, moved, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step writeChooseHeader advanced
      ({ pc := 2, inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, start, ready, written, moved, advanced,
      Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem chooseHeader_dangling_from_anyTape (input output : Tape)
    (hBlank : input.current = none) :
    RunsFor writeChooseHeader
      ({ pc := 4, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have h0 : Step writeChooseHeader
      ({ pc := 4, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next, Configuration.tape, hBlank]
  have h1 : Step writeChooseHeader
      ({ pc := 14, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, writeChooseHeader, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem chooseHeader_finite_loop (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 7 * (input.right.length + 1) + 6 ∧
      RunsFor writeChooseHeader
        ({ pc := 2, inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  cases hCurrent : input.current with
  | none => exact ⟨_, 2, by omega, chooseHeader_blank_from_anyTape input output hCurrent, rfl⟩
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨finish, hRun, hHalt⟩ := chooseHeader_false_from_anyTape input output hCurrent
          exact ⟨finish, 6, by omega, hRun, hHalt⟩
      | true =>
          have hPrefix := chooseHeader_true_prefix_from_anyTape input output hCurrent
          cases hRight : input.right with
          | nil =>
              have hBlank : input.moveRight.current = none := by simp [Tape.moveRight, hRight]
              exact ⟨_, 4, by omega, hPrefix.trans
                (chooseHeader_dangling_from_anyTape input.moveRight output hBlank), rfl⟩
          | cons cell rest =>
              cases cell with
              | none =>
                  have hBlank : input.moveRight.current = none := by simp [Tape.moveRight, hRight]
                  exact ⟨_, 4, by omega, hPrefix.trans
                    (chooseHeader_dangling_from_anyTape input.moveRight output hBlank), rfl⟩
              | some payload =>
                  have hBit : input.moveRight.current = some payload := by simp [Tape.moveRight, hRight]
                  have hBody := chooseHeader_payload_from_anyTape input.moveRight output payload hBit
                  obtain ⟨finish, used, hBound, hRun, hHalt⟩ :=
                    chooseHeader_finite_loop input.moveRight.moveRight (output.write (some true)).moveRight
                  refine ⟨finish, 7 + used, ?_, (hPrefix.trans hBody).trans hRun, hHalt⟩
                  cases rest <;> simp only [Tape.moveRight, hRight, List.length_cons, List.length_nil] at hBound ⊢ <;> omega
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

/-- Linear native stopping bound on arbitrary retained tapes. Internal
blanks, dangling delimiters, and dirty output cells are allowed. This
asserts runtime safety, not validity of the generated choose request. -/
theorem writeChooseHeader_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 7 * input.cells + 8 ∧
      RunsFor writeChooseHeader
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  let written : Configuration :=
    { pc := 1, inputTape := input, outputTape := output.write (some true) }
  let ready : Configuration :=
    { pc := 2, inputTape := input, outputTape := (output.write (some true)).moveRight }
  have h0 : Step writeChooseHeader
      ({ inputTape := input, outputTape := output } : Configuration) written := by
    simp [Step, successors, next, writeChooseHeader, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h1 : Step writeChooseHeader written ready := by
    simp [Step, successors, next, writeChooseHeader, written, ready, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  obtain ⟨finish, used, hBound, hRun, hHalt⟩ :=
    chooseHeader_finite_loop input (output.write (some true)).moveRight
  refine ⟨finish, 2 + used, ?_,
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1).trans hRun, hHalt⟩
  dsimp only [Tape.cells]
  omega

private theorem chooseHeader_suffix_moveRight (input : Tape)
    (hInput : ∃ before bits, input = { Tape.ofBits bits with left := before }) :
    ∃ before bits, input.moveRight = { Tape.ofBits bits with left := before } := by
  rcases hInput with ⟨before, bits, rfl⟩
  refine ⟨(Tape.ofBits bits).current :: before, bits.tail, ?_⟩
  cases bits with
  | nil => rfl
  | cons bit rest => cases rest <;> rfl

private theorem chooseHeader_blankRight_moveRight (output : Tape)
    (hOutput : ∃ blanks, output.right = List.replicate blanks none) :
    ∃ blanks, output.moveRight.right = List.replicate blanks none := by
  obtain ⟨blanks, hBlanks⟩ := hOutput
  refine ⟨blanks - 1, ?_⟩
  cases blanks <;> simp [Tape.moveRight, hBlanks, List.replicate_succ]

private theorem chooseHeader_step_preserves_layout (start finish : Configuration)
    (step : Step writeChooseHeader start finish)
    (hInput : ∃ before bits, start.inputTape = { Tape.ofBits bits with left := before })
    (hOutput : ∃ blanks, start.outputTape.right = List.replicate blanks none) :
    (∃ before bits, finish.inputTape = { Tape.ofBits bits with left := before }) ∧
      (∃ blanks, finish.outputTape.right = List.replicate blanks none) := by
  have hActive : start.halted = false := by
    cases hh : start.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  by_cases hPc : start.pc < 15
  · interval_cases hIndex : start.pc
    all_goals simp [Step, successors, next, hActive, hIndex, writeChooseHeader,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst finish
    all_goals simp only [Configuration.updateTape, Configuration.advance, Tape.write]
    all_goals first
      | exact ⟨hInput, hOutput⟩
      | exact ⟨chooseHeader_suffix_moveRight start.inputTape hInput, hOutput⟩
      | exact ⟨hInput, chooseHeader_blankRight_moveRight start.outputTape hOutput⟩
  · have hNone : writeChooseHeader[start.pc]? = none := by
      apply List.getElem?_eq_none
      change 15 ≤ start.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst finish
    exact ⟨hInput, hOutput⟩

private theorem chooseHeader_run_preserves_layout {start finish : Configuration} {used : Nat}
    (run : RunsFor writeChooseHeader start finish used)
    (hInput : ∃ before bits, start.inputTape = { Tape.ofBits bits with left := before })
    (hOutput : ∃ blanks, start.outputTape.right = List.replicate blanks none) :
    (∃ before bits, finish.inputTape = { Tape.ofBits bits with left := before }) ∧
      (∃ blanks, finish.outputTape.right = List.replicate blanks none) := by
  induction run with
  | zero => exact ⟨hInput, hOutput⟩
  | succ prior last ih =>
      obtain ⟨hMiddleInput, hMiddleOutput⟩ := ih
      exact chooseHeader_step_preserves_layout _ _ last hMiddleInput hMiddleOutput

/-- The header pass on any contiguous raw field retains a contiguous unread
input suffix and blank cells to the right of the output head. Missing field
terminators may leave an incomplete header, but cannot expose dirty cells
in the region that the following payload copy will use. -/
theorem writeChooseHeader_terminates_with_layout (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    ∃ (finish : Configuration) (used : Nat) (saved : List (Option Bool))
      (rest : List Bool) (remainingBlanks : Nat),
      used ≤ 7 * ({ Tape.ofBits bits with left := beforeInput } : Tape).cells + 8 ∧
      RunsFor writeChooseHeader
        ({ inputTape := { Tape.ofBits bits with left := beforeInput },
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { Tape.ofBits rest with left := saved } ∧
      finish.outputTape.right = List.replicate remainingBlanks none := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ := writeChooseHeader_terminates_from_anyTape
    ({ Tape.ofBits bits with left := beforeInput } : Tape)
    ({ left := beforeOutput, right := List.replicate blanks none } : Tape)
  obtain ⟨⟨saved, rest, hInput⟩, ⟨remainingBlanks, hOutput⟩⟩ :=
    chooseHeader_run_preserves_layout hRun ⟨beforeInput, bits, rfl⟩ ⟨blanks, rfl⟩
  exact ⟨finish, used, saved, rest, remainingBlanks, hBound, hRun, hHalted, hInput, hOutput⟩

theorem writeChooseHeader_haltsWithin_anyInput (input : List Bool) :
    HaltsWithin writeChooseHeader input (7 * input.length + 15) := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ :=
    writeChooseHeader_terminates_from_anyTape (Tape.ofBits input) {}
  have hStart : ({ inputTape := Tape.ofBits input } : Configuration) =
      Configuration.initial input := rfl
  rw [hStart] at hRun
  have hCells : (Tape.ofBits input).cells ≤ input.length + 1 := by
    cases input
    · simp [Tape.ofBits, Tape.cells]
    · simp only [Tape.ofBits, Tape.cells, List.length_nil, List.length_map, List.length_cons]
      omega
  have hHalts : HaltsWith writeChooseHeader input finish.outputBits used :=
    ⟨finish, hRun, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit writeChooseHeader_no_randomBit).mono (by omega)

theorem writeChooseHeader_polynomialTime : PolynomialTime writeChooseHeader := by
  refine ⟨fun m => 7 * m + 15, ?_, writeChooseHeader_haltsWithin_anyInput⟩
  exact ((PolynomiallyBounded.const 7).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 15)

/-- Runtime safety of both native passes on arbitrary retained finite
tapes. A malformed field may produce a malformed request; it still stops.
Each write, head move, parser status erasure, and halt is charged. -/
theorem assembleChooseField_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 220 * (input.cells + output.cells) + 300 ∧
      RunsFor assembleChooseField
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨headerFinish, headerTime, hHeaderTime, hHeaderRun, hHeaderHalt⟩ :=
    writeChooseHeader_terminates_from_anyTape input output
  obtain ⟨rewindFinish, rewindTime, hRewindTime, hRewindRun, hRewindHalt, _⟩ :=
    rewindBitstring_terminates_from headerFinish.inputTape headerFinish.outputTape.moveRight
  obtain ⟨readFinish, readTime, hReadTime, hReadRun, hReadHalt⟩ :=
    readDelimited_terminates_from_anyTape rewindFinish.inputTape rewindFinish.outputTape
  let a := writeChooseHeader.asSubroutine 0 16
  let b := rewindBitstring.asSubroutine 17 22
  let k := readDelimited.asSubroutine 22 39
  have hHeader := hHeaderRun.withSubroutine_halted_of_closed
    [] writeChooseHeader ([.moveRight .output] ++ b ++ k ++ [.moveLeft .output, .erase .output, .halt]) 16
    (by change 0 < 15; decide) rfl hHeaderHalt writeChooseHeader_control_closed
  change RunsFor assembleChooseField
    ({ inputTape := input, outputTape := output } : Configuration)
    (headerFinish.resumeAt 16) headerTime at hHeader
  let moved : Configuration :=
    { pc := 17, inputTape := headerFinish.inputTape, outputTape := headerFinish.outputTape.moveRight }
  have hMove : Step assembleChooseField (headerFinish.resumeAt 16) moved := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    (a ++ [.moveRight .output]) rewindBitstring (k ++ [.moveLeft .output, .erase .output, .halt]) 22
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor assembleChooseField moved (rewindFinish.resumeAt 22) rewindTime at hRewind
  have hRead := hReadRun.withSubroutine_halted_of_closed
    (a ++ [.moveRight .output] ++ b) readDelimited [.moveLeft .output, .erase .output, .halt] 39
    (by change 0 < 16; decide) rfl hReadHalt readDelimited_control_closed
  change RunsFor assembleChooseField
    ({ pc := 22, inputTape := rewindFinish.inputTape, outputTape := rewindFinish.outputTape } : Configuration)
    (readFinish.resumeAt 39) readTime at hRead
  have hReadStart : rewindFinish.resumeAt 22 =
      ({ pc := 22, inputTape := rewindFinish.inputTape, outputTape := rewindFinish.outputTape } : Configuration) := rfl
  rw [← hReadStart] at hRead
  let beforeErase : Configuration :=
    { pc := 40, inputTape := readFinish.inputTape, outputTape := readFinish.outputTape.moveLeft }
  let erased : Configuration :=
    { beforeErase with pc := 41, outputTape := beforeErase.outputTape.write none }
  have hBack : Step assembleChooseField (readFinish.resumeAt 39) beforeErase := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      beforeErase, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hErase : Step assembleChooseField beforeErase erased := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, beforeErase, erased,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step assembleChooseField erased { erased with halted := true } := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, beforeErase, erased, Instruction.next]
  have hUntilRewind := (RunsFor.succ hHeader hMove).trans hRewind
  refine ⟨{ erased with halted := true }, headerTime + 1 + rewindTime + readTime + 3, ?_, ?_, rfl⟩
  · have hHeaderStorage := GuardedCompiler.sourceStorage_le_of_run hHeaderRun
    have hRewindStorage := GuardedCompiler.sourceStorage_le_of_run hUntilRewind
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hHeaderStorage hRewindStorage
    have hLeft : headerFinish.inputTape.left.length ≤ headerFinish.inputTape.cells := by
      simp only [Tape.cells]
      omega
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (hUntilRewind.trans hRead) hBack) hErase) hHalt

/-- Two-pass choose assembly retains a contiguous input suffix and a fresh
output frontier even when the delimited key is truncated. Rewind may leave
redundant outer blanks; the resulting layout is therefore stated using
cell equivalence. Both passes are actual charged machine traces. -/
theorem assembleChooseField_terminates_with_layout (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    ∃ (finish : Configuration) (used : Nat) (savedInput : List (Option Bool))
      (rest : List Bool) (savedOutput : List (Option Bool)) (remainingBlanks : Nat),
      used ≤ 220 * (({ Tape.ofBits bits with left := beforeInput } : Tape).cells +
        ({ left := beforeOutput, right := List.replicate blanks none } : Tape).cells) + 300 ∧
      RunsFor assembleChooseField
        ({ inputTape := { Tape.ofBits bits with left := beforeInput },
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape.Equivalent { Tape.ofBits rest with left := savedInput } ∧
      finish.outputTape.Equivalent { left := savedOutput, right := List.replicate remainingBlanks none } := by
  let input : Tape := { Tape.ofBits bits with left := beforeInput }
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  obtain ⟨headerFinish, headerTime, headerBefore, headerRest, headerBlanks,
    hHeaderTime, hHeaderRun, hHeaderHalt, hHeaderInput, hHeaderOutput⟩ :=
    writeChooseHeader_terminates_with_layout beforeInput beforeOutput bits blanks
  have hRecord : headerFinish.outputTape =
      { left := headerFinish.outputTape.left, current := headerFinish.outputTape.current,
        right := List.replicate headerBlanks none } := by
    rw [← hHeaderOutput]
  let readerOutput := headerFinish.outputTape.current :: headerFinish.outputTape.left
  let readerBlanks := headerBlanks - 1
  have hFresh : headerFinish.outputTape.moveRight =
      { left := readerOutput, right := List.replicate readerBlanks none } := by
    calc
      _ = ({ left := headerFinish.outputTape.left, current := headerFinish.outputTape.current, right := List.replicate headerBlanks none } : Tape).moveRight := congrArg Tape.moveRight hRecord
      _ = _ := moveRight_blank_padding _ _ _
  obtain ⟨rewindFinish, leading, saved, hLeading, hRewindRun, hRewindHalt, hRewindInput, hRewindOutput⟩ :=
    rewindBitstring_terminates_from_suffix headerBefore headerRest headerFinish.outputTape.moveRight
  rw [← hHeaderInput] at hRewindRun
  let readerBits := leading ++ headerRest
  have hReaderStart :
      (readDelimitedPaddedStart ([none] ++ saved) readerOutput readerBits readerBlanks).Equivalent
        ({ inputTape := rewindFinish.inputTape, outputTape := rewindFinish.outputTape } : Configuration) := by
    refine ⟨rfl, rfl, hRewindInput.symm, ?_⟩
    rw [hRewindOutput, hFresh]
    exact Tape.Equivalent.refl _
  obtain ⟨readFinish, hReadRun, hReadEq⟩ :=
    (readDelimitedPadded_runs ([none] ++ saved) readerOutput readerBits readerBlanks).exists_equivalent hReaderStart
  have hReadHalt : readFinish.halted = true := by
    simpa only [readDelimitedPaddedFinish] using hReadEq.2.1.symm
  let a := writeChooseHeader.asSubroutine 0 16
  let b := rewindBitstring.asSubroutine 17 22
  let k := readDelimited.asSubroutine 22 39
  have hHeader := hHeaderRun.withSubroutine_halted_of_closed
    [] writeChooseHeader ([.moveRight .output] ++ b ++ k ++ [.moveLeft .output, .erase .output, .halt]) 16
    (by change 0 < 15; decide) rfl hHeaderHalt writeChooseHeader_control_closed
  change RunsFor assembleChooseField
    ({ inputTape := input, outputTape := output } : Configuration)
    (headerFinish.resumeAt 16) headerTime at hHeader
  let moved : Configuration :=
    { pc := 17, inputTape := headerFinish.inputTape, outputTape := headerFinish.outputTape.moveRight }
  have hMove : Step assembleChooseField (headerFinish.resumeAt 16) moved := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    (a ++ [.moveRight .output]) rewindBitstring (k ++ [.moveLeft .output, .erase .output, .halt]) 22
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor assembleChooseField moved (rewindFinish.resumeAt 22) (2 * leading.length + 4) at hRewind
  have hRead := hReadRun.withSubroutine_halted_of_closed
    (a ++ [.moveRight .output] ++ b) readDelimited [.moveLeft .output, .erase .output, .halt] 39
    (by change 0 < 16; decide) rfl hReadHalt readDelimited_control_closed
  change RunsFor assembleChooseField
    ({ pc := 22, inputTape := rewindFinish.inputTape, outputTape := rewindFinish.outputTape } : Configuration)
    (readFinish.resumeAt 39) (readDelimitedSteps readerBits) at hRead
  have hReadStart : rewindFinish.resumeAt 22 =
      ({ pc := 22, inputTape := rewindFinish.inputTape, outputTape := rewindFinish.outputTape } : Configuration) := rfl
  rw [← hReadStart] at hRead
  let beforeErase : Configuration :=
    { pc := 40, inputTape := readFinish.inputTape, outputTape := readFinish.outputTape.moveLeft }
  let erased : Configuration :=
    { beforeErase with pc := 41, outputTape := beforeErase.outputTape.write none }
  have hBack : Step assembleChooseField (readFinish.resumeAt 39) beforeErase := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      beforeErase, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hErase : Step assembleChooseField beforeErase erased := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, beforeErase, erased,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step assembleChooseField erased { erased with halted := true } := by
    simp [Step, successors, next, assembleChooseField, writeChooseHeader, rewindBitstring,
      readDelimited, Program.asSubroutine, Instruction.asSubroutine, beforeErase, erased, Instruction.next]
  have hUntilRewind := (RunsFor.succ hHeader hMove).trans hRewind
  refine ⟨{ erased with halted := true }, headerTime + 1 + (2 * leading.length + 4) + readDelimitedSteps readerBits + 3,
    (scanDelimited readerBits).consumed.reverse.map some ++ ([none] ++ saved),
    (scanDelimited readerBits).tail,
    (scanDelimited readerBits).field.reverse.map some ++ readerOutput,
    readerBlanks - ((scanDelimited readerBits).field.length + 1) + 1,
    ?_, ?_, rfl, ?_, ?_⟩
  · have hHeaderStorage := GuardedCompiler.sourceStorage_le_of_run hHeaderRun
    have hRewindStorage := GuardedCompiler.sourceStorage_le_of_run hUntilRewind
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hHeaderStorage hRewindStorage
    have hLeft : headerFinish.inputTape.left.length ≤ headerFinish.inputTape.cells := by
      simp only [Tape.cells]
      omega
    have hRestLength : headerRest.length ≤ headerFinish.inputTape.cells := by
      rw [hHeaderInput]
      cases headerRest <;> simp [Tape.ofBits, Tape.cells]
    have hReadTime := readDelimitedSteps_le readerBits
    dsimp only [readerBits] at hReadTime
    simp only [List.length_append] at hReadTime
    have hLeadingLength : leading.length ≤ headerFinish.inputTape.left.length := by
      simpa only [hHeaderInput] using hLeading
    dsimp only [input, output, readerBits] at hHeaderStorage hRewindStorage ⊢
    simp only [Tape.cells] at hHeaderTime hHeaderStorage hRewindStorage hLeft hRestLength ⊢
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (hUntilRewind.trans hRead) hBack) hErase) hHalt

  · simpa only [erased, beforeErase, readDelimitedPaddedFinish] using hReadEq.2.2.1.symm
  · simpa only [erased, beforeErase, readDelimitedPaddedFinish, Tape.moveLeft, Tape.write,
      List.replicate_succ] using (hReadEq.2.2.2.symm.moveLeft.write none)

theorem assembleChooseField_haltsWithin_anyInput (input : List Bool) :
    HaltsWithin assembleChooseField input (220 * input.length + 740) := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ :=
    assembleChooseField_terminates_from_anyTape (Tape.ofBits input) {}
  have hStart : ({ inputTape := Tape.ofBits input } : Configuration) = Configuration.initial input := rfl
  rw [hStart] at hRun
  have hCells : (Tape.ofBits input).cells ≤ input.length + 1 := by
    cases input
    · simp [Tape.ofBits, Tape.cells]
    · simp only [Tape.ofBits, Tape.cells, List.length_nil, List.length_map, List.length_cons]
      omega
  have hBlankCells : ({} : Tape).cells = 1 := rfl
  have hHalts : HaltsWith assembleChooseField input finish.outputBits used := ⟨finish, hRun, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit assembleChooseField_no_randomBit).mono (by omega)

theorem assembleChooseField_polynomialTime : PolynomialTime assembleChooseField := by
  refine ⟨fun m => 220 * m + 740, ?_, assembleChooseField_haltsWithin_anyInput⟩
  exact ((PolynomiallyBounded.const 220).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 740)

end Machine
