import Foundation.Machine.Encoding
import Foundation.Machine.PolynomialTime
import Foundation.Machine.SubroutineProbability

namespace Machine

/-- Produce `FiniteBitEncoding.delimit bits` using only one-cell writes,
head moves, branches, and jumps. The input is contiguous and the output is
fresh at and to the right of its head. Saved caller data on either left
prefix is retained. No mathematical encoding function is a machine opcode. -/
def writeDelimited : Program :=
  [.branch .input 11 1 5,
   .write .output true, .moveRight .output,
   .write .output false, .jump 8,
   .write .output true, .moveRight .output, .write .output true,
   .moveRight .input, .moveRight .output, .jump 0,
   .write .output false, .moveRight .output, .halt]

private def writeDelimitedBitSteps (bit : Bool) : Nat := if bit then 7 else 8

/-- Exact charged transition count, including the terminating delimiter and
explicit halt. The two data-bit paths have different lengths. -/
def writeDelimitedSteps : List Bool → Nat
  | [] => 4
  | bit :: rest => writeDelimitedBitSteps bit + writeDelimitedSteps rest

def writeDelimitedStart (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := beforeInput },
    outputTape := { left := beforeOutput } }

def writeDelimitedFinish (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { pc := 13,
    inputTape := { left := bits.reverse.map some ++ beforeInput },
    outputTape := { left := (FiniteBitEncoding.delimit bits).reverse.map some ++ beforeOutput },
    halted := true }

private theorem writeDelimited_one (beforeInput beforeOutput : List (Option Bool))
    (bit : Bool) (rest : List Bool) :
    RunsFor writeDelimited (writeDelimitedStart beforeInput beforeOutput (bit :: rest))
      (writeDelimitedStart (some bit :: beforeInput)
        (some bit :: some true :: beforeOutput) rest) (writeDelimitedBitSteps bit) := by
  let start := writeDelimitedStart beforeInput beforeOutput (bit :: rest)
  let selected : Configuration := { start with pc := if bit then 5 else 1 }
  let marked : Configuration :=
    { selected with
      pc := if bit then 6 else 2,
      outputTape := selected.outputTape.write (some true) }
  let payload : Configuration :=
    { marked with
      pc := if bit then 7 else 3,
      outputTape := marked.outputTape.moveRight }
  let written : Configuration :=
    { payload with
      pc := if bit then 8 else 4,
      outputTape := payload.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 8 }
  let movedInput : Configuration :=
    { ready with pc := 9, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 10, outputTape := movedInput.outputTape.moveRight }
  have hSelect : Step writeDelimited start selected := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected,
      writeDelimitedStart, Tape.ofBits, Instruction.next, Configuration.tape]
  have hMark : Step writeDelimited selected marked := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      writeDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayload : Step writeDelimited marked payload := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, writeDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hWrite : Step writeDelimited payload written := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, written, writeDelimitedStart, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hInput : Step writeDelimited ready movedInput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, writeDelimitedStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step writeDelimited movedInput movedOutput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, movedOutput, writeDelimitedStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step writeDelimited movedOutput
      (writeDelimitedStart (some bit :: beforeInput)
        (some bit :: some true :: beforeOutput) rest) := by
    cases rest <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, written, ready, movedInput, movedOutput, writeDelimitedStart,
      Instruction.next, Tape.ofBits, Tape.moveRight, Tape.write]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hMark) hPayload) hWrite
  cases bit with
  | false =>
      have hJump : Step writeDelimited written ready := by
        simp [Step, successors, next, writeDelimited, written, ready,
          start, selected, marked, payload, writeDelimitedStart, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ prior hInput) hOutput) hBack

theorem writeDelimited_runs (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    RunsFor writeDelimited (writeDelimitedStart beforeInput beforeOutput bits)
      (writeDelimitedFinish beforeInput beforeOutput bits) (writeDelimitedSteps bits) := by
  induction bits generalizing beforeInput beforeOutput with
  | nil =>
      let start := writeDelimitedStart beforeInput beforeOutput []
      let selected : Configuration := { start with pc := 11 }
      let written : Configuration :=
        { selected with pc := 12, outputTape := selected.outputTape.write (some false) }
      let moved : Configuration :=
        { written with pc := 13, outputTape := written.outputTape.moveRight }
      have hSelect : Step writeDelimited start selected := by
        simp [Step, successors, next, writeDelimited, start, selected,
          writeDelimitedStart, Tape.ofBits, Instruction.next, Configuration.tape]
      have hWrite : Step writeDelimited selected written := by
        simp [Step, successors, next, writeDelimited, start, selected, written,
          writeDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hMove : Step writeDelimited written moved := by
        simp [Step, successors, next, writeDelimited, start, selected, written, moved,
          writeDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hHalt : Step writeDelimited moved
          (writeDelimitedFinish beforeInput beforeOutput []) := by
        simp [Step, successors, next, writeDelimited, start, selected, written, moved,
          writeDelimitedStart, writeDelimitedFinish, FiniteBitEncoding.delimit,
          Instruction.next, Tape.ofBits, Tape.write, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hMove) hHalt
  | cons bit rest ih =>
      have tailRun := ih (some bit :: beforeInput) (some bit :: some true :: beforeOutput)
      have hFinish : writeDelimitedFinish (some bit :: beforeInput)
          (some bit :: some true :: beforeOutput) rest =
          writeDelimitedFinish beforeInput beforeOutput (bit :: rest) := by
        simp [writeDelimitedFinish, FiniteBitEncoding.delimit, List.reverse_cons,
          List.map_append, List.append_assoc]
      rw [hFinish] at tailRun
      exact (writeDelimited_one beforeInput beforeOutput bit rest).trans tailRun

theorem writeDelimitedSteps_le (bits : List Bool) :
    writeDelimitedSteps bits ≤ 8 * bits.length + 4 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [writeDelimitedSteps, writeDelimitedBitSteps,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem writeDelimited_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ writeDelimited := by simp [writeDelimited]

theorem writeDelimited_eval (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    evalConfigWithin writeDelimited (writeDelimitedStart beforeInput beforeOutput bits)
      (writeDelimitedSteps bits) =
      PMF.pure (writeDelimitedFinish beforeInput beforeOutput bits) :=
  (writeDelimited_runs beforeInput beforeOutput bits).evalConfigWithin_eq_pure_of_no_randomBit
    writeDelimited_no_randomBit

theorem writeDelimited_control_closed (c d : Configuration)
    (hPc : c.pc < writeDelimited.length) (step : Step writeDelimited c d)
    (_hRunning : d.halted = false) : d.pc < writeDelimited.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 14 at hPc
  change d.pc < 14
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, writeDelimited,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem writeDelimited_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre writeDelimited suffix returnPc)
      ((writeDelimitedStart beforeInput beforeOutput bits).rebasePc pre.length)
      (writeDelimitedSteps bits) =
      PMF.pure ((writeDelimitedFinish beforeInput beforeOutput bits).resumeAt returnPc) :=
  (writeDelimited_runs beforeInput beforeOutput bits).evalConfigWithin_withSubroutine_halted_of_closed
    pre writeDelimited suffix returnPc (by simp [writeDelimitedStart, writeDelimited])
    rfl rfl writeDelimited_control_closed writeDelimited_no_randomBit

theorem writeDelimitedFinish_outputBits (bits : List Bool) :
    (writeDelimitedFinish [] [] bits).outputBits = FiniteBitEncoding.delimit bits := by
  simp [writeDelimitedFinish, Configuration.outputBits, Tape.bits]

theorem writeDelimited_haltsWithin (bits : List Bool) :
    HaltsWithin writeDelimited bits (8 * bits.length + 4) := by
  have hStart : writeDelimitedStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have run := writeDelimited_runs [] [] bits
  rw [hStart] at run
  have hHalt : HaltsWith writeDelimited bits (FiniteBitEncoding.delimit bits)
      (writeDelimitedSteps bits) :=
    ⟨_, run, rfl, writeDelimitedFinish_outputBits bits⟩
  exact (hHalt.haltsWithin_of_no_randomBit writeDelimited_no_randomBit).mono
    (writeDelimitedSteps_le bits)

/-- Framing one field has a worst-case linear bound in total raw input
length. Termination includes an explicit delimiter write and halt. -/
theorem writeDelimited_polynomialTime : PolynomialTime writeDelimited := by
  refine ⟨fun m => 8 * m + 4, ?_, writeDelimited_haltsWithin⟩
  exact ((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 4)

theorem writeDelimited_evalWithin (bits : List Bool) :
    evalWithin writeDelimited bits (8 * bits.length + 4) =
      PMF.pure (some (FiniteBitEncoding.delimit bits)) := by
  have hStart : writeDelimitedStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have run := writeDelimited_runs [] [] bits
  rw [hStart] at run
  have hHalt : HaltsWith writeDelimited bits (FiniteBitEncoding.delimit bits)
      (writeDelimitedSteps bits) :=
    ⟨_, run, rfl, writeDelimitedFinish_outputBits bits⟩
  rw [evalWithin_eq_of_haltsWithin writeDelimited bits
    (8 * bits.length + 4) (writeDelimitedSteps bits)
    (writeDelimited_haltsWithin bits)
    (hHalt.haltsWithin_of_no_randomBit writeDelimited_no_randomBit)]
  exact hHalt.evalWithin_eq_pure_of_no_randomBit writeDelimited_no_randomBit

end Machine
