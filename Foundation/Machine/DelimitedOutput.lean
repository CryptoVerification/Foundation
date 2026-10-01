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

private theorem writeDelimited_cell_run (input output : Tape) (bit : Bool)
    (hCurrent : input.current = some bit) :
    RunsFor writeDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight, outputTape := ((output.write (some true)).moveRight.write (some bit)).moveRight } : Configuration)
      (writeDelimitedBitSteps bit) := by
  let start : Configuration := { inputTape := input, outputTape := output }
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
      Instruction.next, Configuration.tape, hCurrent]
  have hMark : Step writeDelimited selected marked := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayload : Step writeDelimited marked payload := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hWrite : Step writeDelimited payload written := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, written, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hInput : Step writeDelimited ready movedInput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step writeDelimited movedInput movedOutput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step writeDelimited movedOutput
      ({ inputTape := input.moveRight, outputTape := ((output.write (some true)).moveRight.write (some bit)).moveRight } : Configuration) := by
    simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, written, ready, movedInput, movedOutput,
      Instruction.next, Tape.moveRight, Tape.write]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hMark) hPayload) hWrite
  cases bit with
  | false =>
      have hJump : Step writeDelimited written ready := by
        simp [Step, successors, next, writeDelimited, written, ready,
          start, selected, marked, payload, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ prior hInput) hOutput) hBack

private theorem writeDelimited_one (beforeInput beforeOutput : List (Option Bool))
    (bit : Bool) (rest : List Bool) :
    RunsFor writeDelimited (writeDelimitedStart beforeInput beforeOutput (bit :: rest))
      (writeDelimitedStart (some bit :: beforeInput)
        (some bit :: some true :: beforeOutput) rest) (writeDelimitedBitSteps bit) := by
  have run := writeDelimited_cell_run
    ({ Tape.ofBits (bit :: rest) with left := beforeInput } : Tape)
    ({ left := beforeOutput } : Tape) bit rfl
  cases rest <;> simpa [writeDelimitedStart, Tape.ofBits, Tape.moveRight, Tape.write] using run

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


private theorem writeDelimited_blank_run (input output : Tape) (hBlank : input.current = none) :
    RunsFor writeDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 13, inputTape := input, outputTape := (output.write (some false)).moveRight, halted := true } : Configuration) 4 := by
  let selected : Configuration := { pc := 11, inputTape := input, outputTape := output }
  let written : Configuration := { selected with pc := 12, outputTape := output.write (some false) }
  let moved : Configuration := { written with pc := 13, outputTape := written.outputTape.moveRight }
  have a : Step writeDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, writeDelimited, selected, Instruction.next, Configuration.tape, hBlank]
  have b : Step writeDelimited selected written := by
    simp [Step, successors, next, writeDelimited, selected, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step writeDelimited written moved := by
    simp [Step, successors, next, writeDelimited, selected, written, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have d : Step writeDelimited moved
      ({ pc := 13, inputTape := input, outputTape := (output.write (some false)).moveRight, halted := true } : Configuration) := by
    simp [Step, successors, next, writeDelimited, selected, written, moved, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c) d

private theorem writeDelimited_fresh_move (before : List (Option Bool)) (blanks : Nat) (bit : Bool) :
    (({ left := before, right := List.replicate blanks none } : Tape).write (some bit)).moveRight =
      { left := some bit :: before, right := List.replicate (blanks - 1) none } := by
  cases blanks <;> simp [Tape.write, Tape.moveRight, List.replicate_succ]

private theorem writeDelimited_finite_cells (right : List (Option Bool))
    (left : List (Option Bool)) (current : Option Bool) (output : Tape) :
    ∃ finish used, used ≤ 8 * (right.length + 1) + 4 ∧
      RunsFor writeDelimited
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  induction right generalizing left current output with
  | nil =>
      cases current with
      | none =>
          refine ⟨_, 4, by decide, writeDelimited_blank_run _ output rfl, rfl, ?_⟩
          intro before blanks hOutput
          exact ⟨some false :: before, blanks - 1, by
            change (output.write (some false)).moveRight = _
            rw [hOutput, writeDelimited_fresh_move]⟩
      | some bit =>
          let nextOutput := ((output.write (some true)).moveRight.write (some bit)).moveRight
          have first := writeDelimited_cell_run ({ left := left, current := some bit } : Tape) output bit rfl
          have last := writeDelimited_blank_run ({ left := some bit :: left } : Tape) nextOutput rfl
          have run := first.trans (by simpa [Tape.moveRight, nextOutput] using last)
          refine ⟨_, writeDelimitedBitSteps bit + 4, ?_, run, rfl, ?_⟩
          · cases bit <;> decide
          · intro before blanks hOutput
            refine ⟨some false :: some bit :: some true :: before, blanks - 1 - 1 - 1, ?_⟩
            change (nextOutput.write (some false)).moveRight = _
            dsimp only [nextOutput]
            rw [hOutput, writeDelimited_fresh_move, writeDelimited_fresh_move, writeDelimited_fresh_move]
  | cons cell rest ih =>
      cases current with
      | none =>
          refine ⟨_, 4, by omega, writeDelimited_blank_run _ output rfl, rfl, ?_⟩
          intro before blanks hOutput
          exact ⟨some false :: before, blanks - 1, by
            change (output.write (some false)).moveRight = _
            rw [hOutput, writeDelimited_fresh_move]⟩
      | some bit =>
          let nextOutput := ((output.write (some true)).moveRight.write (some bit)).moveRight
          obtain ⟨finish, used, hUsed, tailRun, hHalt, hLayout⟩ := ih (some bit :: left) cell nextOutput
          have first := writeDelimited_cell_run
            ({ left := left, current := some bit, right := cell :: rest } : Tape) output bit rfl
          have run := first.trans (by simpa [Tape.moveRight, nextOutput] using tailRun)
          refine ⟨finish, writeDelimitedBitSteps bit + used, ?_, run, hHalt, ?_⟩
          · cases bit <;> simp only [writeDelimitedBitSteps, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
          · intro before blanks hOutput
            apply hLayout (some bit :: some true :: before) (blanks - 1 - 1)
            dsimp only [nextOutput]
            rw [hOutput, writeDelimited_fresh_move, writeDelimited_fresh_move]

/-- Delimiter writing terminates on every finite input, even with internal
blanks or a dirty output tape. It reads through at most the finite contiguous
input segment, and every marker and payload bit is written by native steps. -/
theorem writeDelimited_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 8 * input.cells + 4 ∧
      RunsFor writeDelimited
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hUsed, run, hHalt, _hLayout⟩ :=
    writeDelimited_finite_cells input.right input.left input.current output
  refine ⟨finish, used, ?_, run, hHalt⟩
  dsimp only [Tape.cells]
  omega

/-- Delimiter writing on an arbitrary finite input retains a fresh output
frontier when that frontier was fresh at entry. Internal input blanks merely
end the native scan; no valid protocol response is assumed. -/
theorem writeDelimited_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining, used ≤ 8 * input.cells + 4 ∧
      RunsFor writeDelimited
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hUsed, run, hHalt, hLayout⟩ :=
    writeDelimited_finite_cells input.right input.left input.current
      { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  refine ⟨finish, used, after, remaining, ?_, run, hHalt, hOutput⟩
  dsimp only [Tape.cells]
  omega


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem writeDelimited_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor writeDelimited
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (8 * input.cells + 4)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    writeDelimited_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted writeDelimited_no_randomBit hBound finish trace

end Machine
