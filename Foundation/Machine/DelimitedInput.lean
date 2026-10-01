import Foundation.Machine.Encoding
import Foundation.Machine.PolynomialTime
import Foundation.Machine.SubroutineProbability

namespace Machine

/-- Read one `FiniteBitEncoding.delimit` field, copying each payload bit to
fresh output cells. A false delimiter advances the input head to the next
field. Blank input, including a dangling true prefix, stops at the failure
halt. A final output bit records success or failure, so an embedded caller
can inspect the status after both halts have returned. Neither input bits nor caller prefixes are overwritten. These are
ordinary one-cell instructions; decoding an element is a separate obligation. -/
def readDelimited : Program :=
  [.branch .input 13 9 1,
   .moveRight .input,
   .branch .input 13 3 5,
   .write .output false, .jump 6,
   .write .output true,
   .moveRight .input, .moveRight .output, .jump 0,
   .moveRight .input,
   .write .output true, .moveRight .output, .halt,
   .write .output false, .moveRight .output, .halt]

/-- A mathematical description of the parser's final tapes, not a machine
instruction or an uncharged parser call. Partial payloads are retained on
failure, and `complete` distinguishes them from a terminated field. -/
structure DelimitedScan where
  field : List Bool
  tail : List Bool
  consumed : List Bool
  complete : Bool
  deriving DecidableEq, Repr

def scanDelimited : List Bool → DelimitedScan
  | [] => ⟨[], [], [], false⟩
  | false :: rest => ⟨[], rest, [false], true⟩
  | [true] => ⟨[], [], [true], false⟩
  | true :: bit :: rest =>
      let result := scanDelimited rest
      { result with
        field := bit :: result.field,
        consumed := true :: bit :: result.consumed }

private def readDelimitedBitSteps (bit : Bool) : Nat := if bit then 7 else 8

/-- Actual transition count, including the final explicit halt. -/
def readDelimitedSteps : List Bool → Nat
  | [] => 4
  | false :: _ => 5
  | [true] => 6
  | true :: bit :: rest => readDelimitedBitSteps bit + readDelimitedSteps rest

private def delimitedState (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat := 0) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := beforeInput },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

/-- Exact invocation layout: the input is contiguous from the current head,
the output is fresh at and to the right of its head, and either tape may have
previously saved data to its left. -/
def readDelimitedStart (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration := delimitedState beforeInput beforeOutput bits

/-- The successful halt is at address 12 and the failure halt at address 15.
The final status bit is immediately to the left of the output head. The
head position and partial copied payload are explicit on failure too. -/
def readDelimitedFinish (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration :=
  let result := scanDelimited bits
  { pc := if result.complete then 12 else 15,
    inputTape := { Tape.ofBits result.tail with
      left := result.consumed.reverse.map some ++ beforeInput },
    outputTape := { left := some result.complete ::
      (result.field.reverse.map some ++ beforeOutput) },
    halted := true }

private theorem emitStatus_run (input : Tape) (beforeOutput : List (Option Bool))
    (status : Bool) (blanks : Nat := 0) :
    RunsFor readDelimited
      ({
        pc := if status then 10 else 13,
        inputTape := input, outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
      ({
        pc := if status then 12 else 15,
        inputTape := input, outputTape := { left := some status :: beforeOutput, right := List.replicate (blanks - 1) none },
        halted := true } : Configuration) 3 := by
  let start : Configuration :=
    { pc := if status then 10 else 13,
      inputTape := input, outputTape := { left := beforeOutput, right := List.replicate blanks none } }
  let written : Configuration :=
    { start with
      pc := if status then 11 else 14,
      outputTape := start.outputTape.write (some status) }
  let moved : Configuration :=
    { written with
      pc := if status then 12 else 15,
      outputTape := written.outputTape.moveRight }
  have hWrite : Step readDelimited start written := by
    cases status <;> simp [Step, successors, next, readDelimited, start, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step readDelimited written moved := by
    cases status <;> simp [Step, successors, next, readDelimited, start, written, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step readDelimited moved
      ({
        pc := if status then 12 else 15,
        inputTape := input, outputTape := { left := some status :: beforeOutput, right := List.replicate (blanks - 1) none },
        halted := true } : Configuration) := by
    cases status <;> cases blanks <;> simp [Step, successors, next, readDelimited, start, written, moved,
      Instruction.next, Tape.write, Tape.moveRight, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hWrite) hMove) hHalt

private theorem readDelimited_one (beforeInput beforeOutput : List (Option Bool))
    (bit : Bool) (rest : List Bool) (blanks : Nat := 0) :
    RunsFor readDelimited
      (delimitedState beforeInput beforeOutput (true :: bit :: rest) blanks)
      (delimitedState (some bit :: some true :: beforeInput)
        (some bit :: beforeOutput) rest (blanks - 1)) (readDelimitedBitSteps bit) := by
  let start := delimitedState beforeInput beforeOutput (true :: bit :: rest) blanks
  let prefixRead : Configuration := { start with pc := 1 }
  let payload : Configuration :=
    { prefixRead with pc := 2, inputTape := prefixRead.inputTape.moveRight }
  let selected : Configuration := { payload with pc := if bit then 5 else 3 }
  let written : Configuration :=
    { selected with
      pc := if bit then 6 else 4,
      outputTape := selected.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 6 }
  let movedInput : Configuration :=
    { ready with pc := 7, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 8, outputTape := movedInput.outputTape.moveRight }
  have hPrefix : Step readDelimited start prefixRead := by
    simp [Step, successors, next, readDelimited, start, prefixRead,
      delimitedState, Tape.ofBits, Instruction.next, Configuration.tape]
  have hPayload : Step readDelimited prefixRead payload := by
    simp [Step, successors, next, readDelimited, start, prefixRead, payload,
      delimitedState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSelect : Step readDelimited payload selected := by
    cases bit <;> simp [Step, successors, next, readDelimited, start, prefixRead,
      payload, selected, delimitedState, Tape.ofBits, Tape.moveRight,
      Instruction.next, Configuration.tape]
  have hWrite : Step readDelimited selected written := by
    cases bit <;> simp [Step, successors, next, readDelimited, start, prefixRead,
      payload, selected, written, delimitedState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hInput : Step readDelimited ready movedInput := by
    simp [Step, successors, next, readDelimited, start, prefixRead, payload,
      selected, written, ready, movedInput, delimitedState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step readDelimited movedInput movedOutput := by
    simp [Step, successors, next, readDelimited, start, prefixRead, payload,
      selected, written, ready, movedInput, movedOutput, delimitedState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step readDelimited movedOutput
      (delimitedState (some bit :: some true :: beforeInput)
        (some bit :: beforeOutput) rest (blanks - 1)) := by
    cases rest <;> cases blanks <;> simp [Step, successors, next, readDelimited, start, prefixRead,
      payload, selected, written, ready, movedInput, movedOutput, delimitedState,
      Instruction.next, Tape.ofBits, Tape.moveRight, Tape.write, List.replicate_succ]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hPrefix) hPayload) hSelect
  cases bit with
  | false =>
      have hJump : Step readDelimited written ready := by
        simp [Step, successors, next, readDelimited, written, ready,
          start, prefixRead, payload, selected, delimitedState, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior hWrite) hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior hWrite) hInput) hOutput) hBack

/-- Invocation on a fresh output region whose explicitly represented
blank cells are retained. The existing sixteen parser instructions are used
unchanged, and arbitrary saved data to the left are preserved. -/
def readDelimitedPaddedStart (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  delimitedState beforeInput beforeOutput bits blanks

theorem readDelimitedPaddedStart_layout (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    readDelimitedPaddedStart beforeInput beforeOutput bits blanks =
      ({
        inputTape := { Tape.ofBits bits with left := beforeInput }
        outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration) := rfl

def readDelimitedPaddedFinish (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  let result := scanDelimited bits
  { pc := if result.complete then 12 else 15,
    inputTape := { Tape.ofBits result.tail with
      left := result.consumed.reverse.map some ++ beforeInput },
    outputTape := {
      left := some result.complete :: (result.field.reverse.map some ++ beforeOutput)
      right := List.replicate (blanks - (result.field.length + 1)) none },
    halted := true }

/-- Native operational trace on every finite input, including malformed
fields. Every bit inspection, output write, head move, jump, and halt is charged. -/
theorem readDelimitedPadded_runs (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor readDelimited (readDelimitedPaddedStart beforeInput beforeOutput bits blanks)
      (readDelimitedPaddedFinish beforeInput beforeOutput bits blanks) (readDelimitedSteps bits) := by
  match bits with
  | [] =>
      let start := delimitedState beforeInput beforeOutput [] blanks
      let selected : Configuration := { start with pc := 13 }
      have hBranch : Step readDelimited start selected := by
        simp [Step, successors, next, readDelimited, start, selected,
          delimitedState, Tape.ofBits, Instruction.next, Configuration.tape]
      have terminal := emitStatus_run start.inputTape beforeOutput false blanks
      simpa [readDelimitedPaddedStart, readDelimitedPaddedFinish, readDelimitedSteps, scanDelimited,
        selected, start, delimitedState] using
        (RunsFor.succ (RunsFor.zero _) hBranch).trans terminal
  | false :: rest =>
      let start := delimitedState beforeInput beforeOutput (false :: rest) blanks
      let selected : Configuration := { start with pc := 9 }
      let advanced : Configuration :=
        { selected with pc := 10, inputTape := selected.inputTape.moveRight }
      have hBranch : Step readDelimited start selected := by
        simp [Step, successors, next, readDelimited, start, selected,
          delimitedState, Tape.ofBits, Instruction.next, Configuration.tape]
      have hMove : Step readDelimited selected advanced := by
        simp [Step, successors, next, readDelimited, start, selected, advanced,
          delimitedState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have terminal := emitStatus_run advanced.inputTape beforeOutput true blanks
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hMove).trans terminal
      cases rest <;> simpa [readDelimitedPaddedStart, readDelimitedPaddedFinish, readDelimitedSteps,
        scanDelimited, selected, advanced, start, delimitedState, Tape.ofBits,
        Tape.moveRight] using run
  | [true] =>
      let start := delimitedState beforeInput beforeOutput [true] blanks
      let selected : Configuration := { start with pc := 1 }
      let advanced : Configuration :=
        { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      let failed : Configuration := { advanced with pc := 13 }
      have hBranch : Step readDelimited start selected := by
        simp [Step, successors, next, readDelimited, start, selected,
          delimitedState, Tape.ofBits, Instruction.next, Configuration.tape]
      have hMove : Step readDelimited selected advanced := by
        simp [Step, successors, next, readDelimited, start, selected, advanced,
          delimitedState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hFail : Step readDelimited advanced failed := by
        simp [Step, successors, next, readDelimited, start, selected, advanced,
          failed, delimitedState, Instruction.next, Tape.ofBits, Tape.moveRight,
          Configuration.tape]
      have terminal := emitStatus_run failed.inputTape beforeOutput false blanks
      simpa [readDelimitedPaddedStart, readDelimitedPaddedFinish, readDelimitedSteps, scanDelimited,
        selected, failed, advanced, start, delimitedState, Tape.ofBits, Tape.moveRight] using
        (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hMove) hFail).trans
          terminal
  | true :: bit :: rest =>
      have tailRun := readDelimitedPadded_runs (some bit :: some true :: beforeInput)
        (some bit :: beforeOutput) rest (blanks - 1)
      have hFinish : readDelimitedPaddedFinish (some bit :: some true :: beforeInput)
          (some bit :: beforeOutput) rest (blanks - 1) =
          readDelimitedPaddedFinish beforeInput beforeOutput (true :: bit :: rest) blanks := by
        have hSubtract : blanks - 1 - ((scanDelimited rest).field.length + 1) =
            blanks - ((scanDelimited rest).field.length + 1 + 1) := by omega
        simp [readDelimitedPaddedFinish, scanDelimited, List.reverse_cons,
          List.map_append, List.append_assoc, hSubtract]
        rfl
      rw [hFinish] at tailRun
      exact (readDelimited_one beforeInput beforeOutput bit rest blanks).trans tailRun
termination_by bits.length

/-- Native operational trace on every finite input, including malformed
fields. Every bit inspection, output write, head move, jump, and halt is charged. -/
theorem readDelimited_runs (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    RunsFor readDelimited (readDelimitedStart beforeInput beforeOutput bits)
      (readDelimitedFinish beforeInput beforeOutput bits) (readDelimitedSteps bits) := by
  simpa [readDelimitedPaddedStart, readDelimitedStart, readDelimitedPaddedFinish,
    readDelimitedFinish] using readDelimitedPadded_runs beforeInput beforeOutput bits 0

theorem scanDelimited_complete (field tail : List Bool) :
    scanDelimited (FiniteBitEncoding.delimit field ++ tail) =
      ⟨field, tail, FiniteBitEncoding.delimit field, true⟩ := by
  induction field with
  | nil => rfl
  | cons bit rest ih => simp [FiniteBitEncoding.delimit, scanDelimited, ih]

/-- The successful native parse implements the existing protocol splitter.
Failure stays distinguishable from a valid empty field. -/
theorem scanDelimited_undelimit (bits : List Bool) :
    FiniteBitEncoding.undelimit bits =
      if (scanDelimited bits).complete then
        some ((scanDelimited bits).field, (scanDelimited bits).tail) else none := by
  match bits with
  | [] => rfl
  | false :: rest => rfl
  | [true] => rfl
  | true :: bit :: rest =>
      simp only [FiniteBitEncoding.undelimit, scanDelimited,
        scanDelimited_undelimit rest]
      by_cases h : (scanDelimited rest).complete = true <;> simp [h]
termination_by bits.length

theorem readDelimitedSteps_le (bits : List Bool) :
    readDelimitedSteps bits ≤ 4 * bits.length + 5 := by
  match bits with
  | [] => decide
  | false :: rest => simp [readDelimitedSteps]
  | [true] => decide
  | true :: bit :: rest =>
      have h := readDelimitedSteps_le rest
      cases bit <;> simp only [readDelimitedSteps, readDelimitedBitSteps,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
termination_by bits.length

theorem readDelimited_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ readDelimited := by simp [readDelimited]

/-- Complete configuration probability law; input tails, saved prefixes,
head positions, and malformed-input status are retained. -/
theorem readDelimited_eval (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    evalConfigWithin readDelimited (readDelimitedStart beforeInput beforeOutput bits)
      (readDelimitedSteps bits) =
      PMF.pure (readDelimitedFinish beforeInput beforeOutput bits) :=
  (readDelimited_runs beforeInput beforeOutput bits).evalConfigWithin_eq_pure_of_no_randomBit
    readDelimited_no_randomBit

/-- Exact contextual semantics with explicit output blank padding. Both
success and malformed-input halts keep the actual tape representation. -/
theorem readDelimitedPadded_eval (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin readDelimited (readDelimitedPaddedStart beforeInput beforeOutput bits blanks)
      (readDelimitedSteps bits) = PMF.pure (readDelimitedPaddedFinish beforeInput beforeOutput bits blanks) :=
  (readDelimitedPadded_runs beforeInput beforeOutput bits blanks).evalConfigWithin_eq_pure_of_no_randomBit
    readDelimited_no_randomBit

theorem readDelimitedFinish_outputBits (bits : List Bool) :
    (readDelimitedFinish [] [] bits).outputBits =
      (scanDelimited bits).field ++ [(scanDelimited bits).complete] := by
  simp [readDelimitedFinish, Configuration.outputBits, Tape.bits]

/-- The status stays on a tape cell when subroutine halts are translated
to caller returns; it is not merely the standalone program counter. -/
theorem readDelimitedFinish_status (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    (readDelimitedFinish beforeInput beforeOutput bits).outputTape.left.head? =
      some (some (scanDelimited bits).complete) := rfl

theorem readDelimited_control_closed (c d : Configuration)
    (hPc : c.pc < readDelimited.length) (step : Step readDelimited c d)
    (_hRunning : d.halted = false) : d.pc < readDelimited.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 16 at hPc
  change d.pc < 16
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, readDelimited,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The same exact native tape computation inside arbitrary surrounding
code, including randomized callers. Both completion paths return with their
explicit output status bit. -/
theorem readDelimited_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre readDelimited suffix returnPc)
      ((readDelimitedStart beforeInput beforeOutput bits).rebasePc pre.length)
      (readDelimitedSteps bits) =
      PMF.pure ((readDelimitedFinish beforeInput beforeOutput bits).resumeAt returnPc) :=
  (readDelimited_runs beforeInput beforeOutput bits).evalConfigWithin_withSubroutine_halted_of_closed
    pre readDelimited suffix returnPc (by simp [readDelimitedStart, delimitedState, readDelimited])
    rfl rfl readDelimited_control_closed readDelimited_no_randomBit

theorem readDelimited_haltsWithin (bits : List Bool) :
    HaltsWithin readDelimited bits (4 * bits.length + 5) := by
  have hStart : readDelimitedStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have run := readDelimited_runs [] [] bits
  rw [hStart] at run
  have hHalt : HaltsWith readDelimited bits
      (readDelimitedFinish [] [] bits).outputBits (readDelimitedSteps bits) :=
    ⟨_, run, rfl, rfl⟩
  exact (hHalt.haltsWithin_of_no_randomBit readDelimited_no_randomBit).mono
    (readDelimitedSteps_le bits)

/-- All finite inputs and all branches halt within a linear transition
bound. This says nothing about a cryptographic element decoder. -/
theorem readDelimited_polynomialTime : PolynomialTime readDelimited := by
  refine ⟨fun m => 4 * m + 5, ?_, readDelimited_haltsWithin⟩
  exact ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 5)

/-- The ordinary output is the partial decoded field followed by its
success bit, even on malformed input. All possible branches have stopped
before this common linear bound is observed. -/
theorem readDelimited_evalWithin (bits : List Bool) :
    evalWithin readDelimited bits (4 * bits.length + 5) =
      PMF.pure (some ((scanDelimited bits).field ++ [(scanDelimited bits).complete])) := by
  have hStart : readDelimitedStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have run := readDelimited_runs [] [] bits
  rw [hStart] at run
  have hHalt : HaltsWith readDelimited bits
      ((scanDelimited bits).field ++ [(scanDelimited bits).complete])
      (readDelimitedSteps bits) :=
    ⟨_, run, rfl, readDelimitedFinish_outputBits bits⟩
  rw [evalWithin_eq_of_haltsWithin readDelimited bits
    (4 * bits.length + 5) (readDelimitedSteps bits)
    (readDelimited_haltsWithin bits)
    (hHalt.haltsWithin_of_no_randomBit readDelimited_no_randomBit)]
  exact hHalt.evalWithin_eq_pure_of_no_randomBit readDelimited_no_randomBit



private def delimitedContextTape (before cells : List (Option Bool)) : Tape :=
  match cells with
  | [] => { left := before }
  | cell :: rest => { left := before, current := cell, right := rest }

/-- The existing parser on a canonical field followed by arbitrary cells,
including blank separators and stored caller data. Its output region is fresh.
This layout is a mathematical fixture, not a new tape-loading instruction. -/
def readDelimitedContextStart (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) : Configuration :=
  { inputTape := delimitedContextTape beforeInput
      ((FiniteBitEncoding.delimit field).map some ++ tail),
    outputTape := { left := beforeOutput } }

def readDelimitedContextFinish (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) : Configuration :=
  { pc := 12,
    inputTape := delimitedContextTape
      ((FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput) tail,
    outputTape := { left := some true :: (field.reverse.map some ++ beforeOutput) },
    halted := true }

private theorem readDelimited_context_bit (beforeInput beforeOutput tail : List (Option Bool))
    (bit : Bool) (rest : List Bool) :
    RunsFor readDelimited (readDelimitedContextStart beforeInput beforeOutput (bit :: rest) tail)
      (readDelimitedContextStart (some bit :: some true :: beforeInput)
        (some bit :: beforeOutput) rest tail) (readDelimitedBitSteps bit) := by
  let start := readDelimitedContextStart beforeInput beforeOutput (bit :: rest) tail
  let prefixRead : Configuration := { start with pc := 1 }
  let payload : Configuration := { prefixRead with pc := 2, inputTape := prefixRead.inputTape.moveRight }
  let selected : Configuration := { payload with pc := if bit then 5 else 3 }
  let written : Configuration :=
    { selected with pc := if bit then 6 else 4, outputTape := selected.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 6 }
  let movedInput : Configuration := { ready with pc := 7, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 8, outputTape := movedInput.outputTape.moveRight }
  have h0 : Step readDelimited start prefixRead := by
    simp [Step, successors, next, readDelimited, start, prefixRead, readDelimitedContextStart,
      delimitedContextTape, FiniteBitEncoding.delimit, Instruction.next, Configuration.tape]
  have h1 : Step readDelimited prefixRead payload := by
    simp [Step, successors, next, readDelimited, start, prefixRead, payload,
      readDelimitedContextStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step readDelimited payload selected := by
    cases bit <;> simp [Step, successors, next, readDelimited, start, prefixRead, payload, selected,
      readDelimitedContextStart, delimitedContextTape, FiniteBitEncoding.delimit,
      Tape.moveRight, Instruction.next, Configuration.tape]
  have h3 : Step readDelimited selected written := by
    cases bit <;> simp [Step, successors, next, readDelimited, selected, written,
      start, prefixRead, payload, readDelimitedContextStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step readDelimited ready movedInput := by
    simp [Step, successors, next, readDelimited, ready, movedInput,
      start, prefixRead, payload, selected, written, ready, readDelimitedContextStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step readDelimited movedInput movedOutput := by
    simp [Step, successors, next, readDelimited, movedInput, movedOutput,
      start, prefixRead, payload, selected, written, ready, readDelimitedContextStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h6 : Step readDelimited movedOutput
      (readDelimitedContextStart (some bit :: some true :: beforeInput)
        (some bit :: beforeOutput) rest tail) := by
    cases rest <;> simp [Step, successors, next, readDelimited, start, prefixRead, payload,
      selected, written, ready, movedInput, movedOutput, readDelimitedContextStart,
      delimitedContextTape, FiniteBitEncoding.delimit, Instruction.next, Tape.moveRight, Tape.write]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  cases bit with
  | false =>
      have hJump : Step readDelimited written ready := by
        simp [Step, successors, next, readDelimited, written, ready, selected, payload, prefixRead, start, readDelimitedContextStart, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior h3) hJump) h4) h5) h6
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at h4
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ prior h3) h4) h5) h6

/-- Same native parser and charged reads/writes as before. The successful
scan ends at the very first following cell and preserves all cells thereafter. -/
theorem readDelimitedContext_runs (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    RunsFor readDelimited (readDelimitedContextStart beforeInput beforeOutput field tail)
      (readDelimitedContextFinish beforeInput beforeOutput field tail)
      (readDelimitedSteps (FiniteBitEncoding.delimit field)) := by
  induction field generalizing beforeInput beforeOutput with
  | nil =>
      let start := readDelimitedContextStart beforeInput beforeOutput [] tail
      let selected : Configuration := { start with pc := 9 }
      let advanced : Configuration := { selected with pc := 10, inputTape := selected.inputTape.moveRight }
      have h0 : Step readDelimited start selected := by
        simp [Step, successors, next, readDelimited, start, selected, readDelimitedContextStart,
          delimitedContextTape, FiniteBitEncoding.delimit, Instruction.next, Configuration.tape]
      have h1 : Step readDelimited selected advanced := by
        simp [Step, successors, next, readDelimited, selected, advanced,
          start, readDelimitedContextStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have terminal := emitStatus_run advanced.inputTape beforeOutput true 0
      cases tail <;> simpa [start, selected, advanced, readDelimitedContextStart,
        readDelimitedContextFinish, delimitedContextTape, FiniteBitEncoding.delimit,
        Tape.moveRight, readDelimitedSteps] using
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1).trans terminal
  | cons bit rest ih =>
      have run := (readDelimited_context_bit beforeInput beforeOutput tail bit rest).trans
        (ih (some bit :: some true :: beforeInput) (some bit :: beforeOutput))
      have hFinish : readDelimitedContextFinish (some bit :: some true :: beforeInput)
          (some bit :: beforeOutput) rest tail =
          readDelimitedContextFinish beforeInput beforeOutput (bit :: rest) tail := by
        simp [readDelimitedContextFinish, FiniteBitEncoding.delimit, List.reverse_cons,
          List.map_append, List.append_assoc]
      rw [hFinish] at run
      exact run

theorem readDelimitedContext_eval (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    evalConfigWithin readDelimited (readDelimitedContextStart beforeInput beforeOutput field tail)
      (readDelimitedSteps (FiniteBitEncoding.delimit field)) =
      PMF.pure (readDelimitedContextFinish beforeInput beforeOutput field tail) :=
  (readDelimitedContext_runs beforeInput beforeOutput field tail).evalConfigWithin_eq_pure_of_no_randomBit
    readDelimited_no_randomBit

theorem readDelimitedContextStart_layout (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    readDelimitedContextStart beforeInput beforeOutput field tail =
      { inputTape := { ({ right := (FiniteBitEncoding.delimit field).map some ++ tail } : Tape).moveRight
          with left := beforeInput }, outputTape := { left := beforeOutput } } := by
  cases field <;> simp [readDelimitedContextStart, delimitedContextTape,
    FiniteBitEncoding.delimit, Tape.moveRight]

theorem readDelimitedContextFinish_input (beforeInput beforeOutput : List (Option Bool))
    (field : List Bool) (tail : List (Option Bool)) :
    (readDelimitedContextFinish beforeInput beforeOutput field tail).inputTape =
      { ({ right := tail } : Tape).moveRight with
        left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput } := by
  cases tail <;> rfl

private theorem emitStatus_from_anyTape (input output : Tape) (status : Bool) :
    RunsFor readDelimited
      ({ pc := if status then 10 else 13, inputTape := input, outputTape := output } : Configuration)
      ({ pc := if status then 12 else 15, inputTape := input,
         outputTape := (output.write (some status)).moveRight, halted := true } : Configuration) 3 := by
  let start : Configuration :=
    { pc := if status then 10 else 13, inputTape := input, outputTape := output }
  let written : Configuration :=
    { start with pc := if status then 11 else 14, outputTape := output.write (some status) }
  let advanced : Configuration :=
    { written with pc := if status then 12 else 15, outputTape := written.outputTape.moveRight }
  have h0 : Step readDelimited start written := by
    cases status <;> simp [Step, successors, next, readDelimited, start, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step readDelimited written advanced := by
    cases status <;> simp [Step, successors, next, readDelimited, start, written, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step readDelimited advanced { advanced with halted := true } := by
    cases status <;> simp [Step, successors, next, readDelimited, start, written, advanced, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2

private theorem readDelimited_blank_from_anyTape (input output : Tape)
    (hBlank : input.current = none) :
    ∃ finish, RunsFor readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      finish 4 ∧ finish.halted = true ∧
      finish.outputTape = (output.write (some false)).moveRight := by
  have h0 : Step readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 13, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, (RunsFor.succ (RunsFor.zero _) h0).trans
    (emitStatus_from_anyTape input output false), rfl, rfl⟩

private theorem readDelimited_false_from_anyTape (input output : Tape)
    (hFalse : input.current = some false) :
    ∃ finish, RunsFor readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      finish 5 ∧ finish.halted = true ∧
      finish.outputTape = (output.write (some true)).moveRight := by
  have h0 : Step readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 9, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next, Configuration.tape, hFalse]
  have h1 : Step readDelimited ({ pc := 9, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 10, inputTape := input.moveRight, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  exact ⟨_, (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1).trans
    (emitStatus_from_anyTape input.moveRight output true), rfl, rfl⟩

private theorem readDelimited_true_prefix_from_anyTape (input output : Tape)
    (hTrue : input.current = some true) :
    RunsFor readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 2, inputTape := input.moveRight, outputTape := output } : Configuration) 2 := by
  have h0 : Step readDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 1, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next, Configuration.tape, hTrue]
  have h1 : Step readDelimited ({ pc := 1, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 2, inputTape := input.moveRight, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem readDelimited_dangling_from_anyTape (input output : Tape)
    (hBlank : input.current = none) :
    ∃ finish, RunsFor readDelimited
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      finish 4 ∧ finish.halted = true ∧
      finish.outputTape = (output.write (some false)).moveRight := by
  have h0 : Step readDelimited ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 13, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, readDelimited, Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, (RunsFor.succ (RunsFor.zero _) h0).trans
    (emitStatus_from_anyTape input output false), rfl, rfl⟩

private theorem readDelimited_payload_from_anyTape (input output : Tape) (bit : Bool)
    (hBit : input.current = some bit) :
    RunsFor readDelimited
      ({ pc := 2, inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight, outputTape := (output.write (some bit)).moveRight } : Configuration)
      (if bit then 5 else 6) := by
  let start : Configuration := { pc := 2, inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := if bit then 5 else 3 }
  let written : Configuration := { start with pc := if bit then 6 else 4, outputTape := output.write (some bit) }
  let ready : Configuration := { written with pc := 6 }
  let moved : Configuration := { ready with pc := 7, inputTape := input.moveRight }
  let advanced : Configuration := { moved with pc := 8, outputTape := written.outputTape.moveRight }
  have h0 : Step readDelimited start selected := by
    cases bit <;> simp [Step, successors, next, readDelimited, start, selected,
      Instruction.next, Configuration.tape, hBit]
  have h1 : Step readDelimited selected written := by
    cases bit <;> simp [Step, successors, next, readDelimited, start, selected, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step readDelimited ready moved := by
    simp [Step, successors, next, readDelimited, start, written, ready, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step readDelimited moved advanced := by
    simp [Step, successors, next, readDelimited, start, written, ready, moved, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step readDelimited advanced
      ({ inputTape := input.moveRight, outputTape := (output.write (some bit)).moveRight } : Configuration) := by
    simp [Step, successors, next, readDelimited, start, written, ready, moved, advanced, Instruction.next]
  cases bit with
  | false =>
      have hJump : Step readDelimited written ready := by
        simp [Step, successors, next, readDelimited, start, written, ready, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) hJump) h2) h3) h4
  | true =>
      have hReady : ready = written := rfl
      rw [hReady] at h2
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem readDelimited_finite_cells (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 8 * (input.right.length + 1) + 6 ∧
      RunsFor readDelimited ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∀ saved blanks, output = { left := saved, right := List.replicate blanks none } →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none }) := by
  cases hCurrent : input.current with
  | none =>
      obtain ⟨finish, hRun, hHalt, hOutput⟩ := readDelimited_blank_from_anyTape input output hCurrent
      refine ⟨finish, 4, by omega, hRun, hHalt, ?_⟩
      intro saved blanks hFresh
      refine ⟨some false :: saved, blanks - 1, ?_⟩
      cases blanks <;> simp [hOutput, hFresh, Tape.write, Tape.moveRight, List.replicate_succ]
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨finish, hRun, hHalt, hOutput⟩ := readDelimited_false_from_anyTape input output hCurrent
          refine ⟨finish, 5, by omega, hRun, hHalt, ?_⟩
          intro saved blanks hFresh
          refine ⟨some true :: saved, blanks - 1, ?_⟩
          cases blanks <;> simp [hOutput, hFresh, Tape.write, Tape.moveRight, List.replicate_succ]
      | true =>
          have hPrefix := readDelimited_true_prefix_from_anyTape input output hCurrent
          cases hRight : input.right with
          | nil =>
              have hBlank : input.moveRight.current = none := by simp [Tape.moveRight, hRight]
              obtain ⟨finish, hRun, hHalt, hOutput⟩ := readDelimited_dangling_from_anyTape input.moveRight output hBlank
              refine ⟨finish, 6, by omega, hPrefix.trans hRun, hHalt, ?_⟩
              intro saved blanks hFresh
              refine ⟨some false :: saved, blanks - 1, ?_⟩
              cases blanks <;> simp [hOutput, hFresh, Tape.write, Tape.moveRight, List.replicate_succ]
          | cons cell rest =>
              cases cell with
              | none =>
                  have hBlank : input.moveRight.current = none := by simp [Tape.moveRight, hRight]
                  obtain ⟨finish, hRun, hHalt, hOutput⟩ := readDelimited_dangling_from_anyTape input.moveRight output hBlank
                  refine ⟨finish, 6, by omega, hPrefix.trans hRun, hHalt, ?_⟩
                  intro saved blanks hFresh
                  refine ⟨some false :: saved, blanks - 1, ?_⟩
                  cases blanks <;> simp [hOutput, hFresh, Tape.write, Tape.moveRight, List.replicate_succ]
              | some payload =>
                  have hBit : input.moveRight.current = some payload := by simp [Tape.moveRight, hRight]
                  have hBody := readDelimited_payload_from_anyTape input.moveRight output payload hBit
                  obtain ⟨finish, used, hBound, hRun, hHalt, hLayout⟩ := readDelimited_finite_cells
                    input.moveRight.moveRight (output.write (some payload)).moveRight
                  refine ⟨finish, 2 + (if payload then 5 else 6) + used, ?_,
                    (hPrefix.trans hBody).trans hRun, hHalt, ?_⟩
                  · cases rest <;> cases payload <;>
                    simp only [Tape.moveRight, hRight, List.length_cons, List.length_nil,
                      Bool.false_eq_true, ↓reduceIte] at hBound ⊢ <;> omega
                  · intro saved blanks hFresh
                    apply hLayout (some payload :: saved) (blanks - 1)
                    cases blanks <;> simp [hFresh, Tape.write, Tape.moveRight, List.replicate_succ]
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

/-- Runtime safety of the native parser on arbitrary retained finite tapes.
Internal blanks and dirty output regions are permitted: the scan stops at
the first input blank or false delimiter, and emits its native status bit.
This assertion does not turn malformed input into a valid decoded field. -/
theorem readDelimited_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 8 * input.cells + 6 ∧
      RunsFor readDelimited ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, hRun, hHalt, _⟩ := readDelimited_finite_cells input output
  refine ⟨finish, used, ?_, hRun, hHalt⟩
  dsimp only [Tape.cells]
  omega

/-- Even a failed parse leaves a fresh output frontier when its original
output region was fresh. The input may contain internal blanks or a dangling
marker; only the native copying/status instructions determine this layout. -/
theorem readDelimited_terminates_with_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 8 * input.cells + 6 ∧
      RunsFor readDelimited
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, hRun, hHalt, hLayout⟩ :=
    readDelimited_finite_cells input { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout savedOutput blanks rfl
  refine ⟨finish, used, after, remaining, ?_, hRun, hHalt, hOutput⟩
  dsimp only [Tape.cells]
  omega

end Machine
