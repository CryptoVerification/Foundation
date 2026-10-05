import Foundation.Crypto.Semantics.Machine.BinaryIsOne
import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Foundation.Crypto.Semantics.Machine.PolynomialTime

namespace Machine.BinaryIsOneInPlace

/-- Consume a finite little-endian bitstring on the output tape, erase every
cell that it occupied, and leave only the Boolean test result there. The
other tape is untouched, so this routine can inspect an arithmetic result
without making an uncharged copy of either tape. -/
def program : Program :=
  [.branch .output 10 10 1,
   .erase .output,
   .moveRight .output,
   .branch .output 7 4 10,
   .erase .output,
   .moveRight .output,
   .jump 3,
   .write .output true,
   .halt,
   .halt,
   .branch .output 14 11 11,
   .erase .output,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .halt]

/-- This predicate is the numeric one test, even for redundant high zeroes. -/
def accepts (bits : List Bool) : Bool := BinaryIsOne.accepts bits

theorem accepts_iff_value_one (bits : List Bool) :
    accepts bits = true ↔ Binary.value bits = 1 :=
  BinaryIsOne.accepts_iff_value_one bits

def budget (length : Nat) : Nat := 6 * (length + 1) + 4

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private def state (pc : Nat) (other : Tape) (erased : Nat)
    (remaining : List Bool) : Configuration :=
  { pc := pc, inputTape := other,
    outputTape := { Tape.ofBits remaining with
      left := List.replicate erased none } }

private def finish (other : Tape) (erased : Nat) (accepted : Bool) : Configuration :=
  { pc := if accepted then 8 else 15, inputTape := other,
    outputTape := { left := List.replicate erased none, current := some accepted },
    halted := true }

private theorem finish_output (other : Tape) (erased : Nat) (accepted : Bool) :
    (finish other erased accepted).outputBits = [accepted] := by
  simp [finish, Configuration.outputBits, Tape.bits]

private theorem good_empty (other : Tape) (erased : Nat) :
    RunsFor program (state 3 other erased []) (finish other erased true) 3 := by
  let start := state 3 other erased []
  let selected : Configuration := { start with pc := 7 }
  let written : Configuration :=
    { selected with pc := 8, outputTape := selected.outputTape.write (some true) }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, state,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (finish other erased true) := by
    simp [Step, successors, next, program, start, selected, written, finish,
      state, Instruction.next, Tape.write, Tape.ofBits]
  exact ((RunsFor.zero _).succ hBranch).succ hWrite |>.succ hHalt

private theorem bad_empty (other : Tape) (erased : Nat) :
    RunsFor program (state 10 other erased []) (finish other erased false) 3 := by
  let start := state 10 other erased []
  let selected : Configuration := { start with pc := 14 }
  let written : Configuration :=
    { selected with pc := 15, outputTape := selected.outputTape.write (some false) }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, state,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (finish other erased false) := by
    simp [Step, successors, next, program, start, selected, written, finish,
      state, Instruction.next, Tape.write, Tape.ofBits]
  exact ((RunsFor.zero _).succ hBranch).succ hWrite |>.succ hHalt

private theorem bad_bit (other : Tape) (erased : Nat)
    (bit : Bool) (rest : List Bool) :
    RunsFor program (state 10 other erased (bit :: rest))
      (state 10 other (erased + 1) rest) 4 := by
  let start := state 10 other erased (bit :: rest)
  let selected : Configuration := { start with pc := 11 }
  let cleared : Configuration :=
    { selected with pc := 12, outputTape := selected.outputTape.write none }
  let moved : Configuration :=
    { cleared with pc := 13, outputTape := cleared.outputTape.moveRight }
  have hBranch : Step program start selected := by
    cases bit <;>
      simp [Step, successors, next, program, start, selected, state,
        Instruction.next, Configuration.tape, Tape.ofBits]
  have hErase : Step program selected cleared := by
    simp [Step, successors, next, program, start, selected, cleared, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step program cleared moved := by
    simp [Step, successors, next, program, start, selected, cleared, moved, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hJump : Step program moved (state 10 other (erased + 1) rest) := by
    cases rest <;>
      simp [Step, successors, next, program, start, selected, cleared, moved, state,
        Instruction.next, Tape.moveRight, Tape.write, Tape.ofBits,
        List.replicate_succ]
  exact (((RunsFor.zero _).succ hBranch).succ hErase).succ hMove |>.succ hJump

private theorem good_false (other : Tape) (erased : Nat) (rest : List Bool) :
    RunsFor program (state 3 other erased (false :: rest))
      (state 3 other (erased + 1) rest) 4 := by
  let start := state 3 other erased (false :: rest)
  let selected : Configuration := { start with pc := 4 }
  let cleared : Configuration :=
    { selected with pc := 5, outputTape := selected.outputTape.write none }
  let moved : Configuration :=
    { cleared with pc := 6, outputTape := cleared.outputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, state,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hErase : Step program selected cleared := by
    simp [Step, successors, next, program, start, selected, cleared, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step program cleared moved := by
    simp [Step, successors, next, program, start, selected, cleared, moved, state,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hJump : Step program moved (state 3 other (erased + 1) rest) := by
    cases rest <;>
      simp [Step, successors, next, program, start, selected, cleared, moved, state,
        Instruction.next, Tape.moveRight, Tape.write, Tape.ofBits,
        List.replicate_succ]
  exact (((RunsFor.zero _).succ hBranch).succ hErase).succ hMove |>.succ hJump

private theorem good_true (other : Tape) (erased : Nat) (rest : List Bool) :
    RunsFor program (state 3 other erased (true :: rest))
      (state 10 other (erased + 1) rest) 5 := by
  let start := state 3 other erased (true :: rest)
  let selected : Configuration := { start with pc := 10 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, state,
      Instruction.next, Configuration.tape, Tape.ofBits]
  exact (RunsFor.zero _).succ hBranch |>.trans (bad_bit other erased true rest)

private theorem bad_runs (other : Tape) (erased : Nat) (bits : List Bool) :
    ∃ used, used ≤ 4 * bits.length + 3 ∧
      RunsFor program (state 10 other erased bits)
        (finish other (erased + bits.length) false) used := by
  induction bits generalizing erased with
  | nil => exact ⟨3, by simp, by simpa using bad_empty other erased⟩
  | cons bit rest ih =>
      obtain ⟨used, hUsed, run⟩ := ih (erased + 1)
      refine ⟨4 + used, by simp; omega, ?_⟩
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using (bad_bit other erased bit rest).trans run

private theorem good_runs (other : Tape) (erased : Nat) (bits : List Bool) :
    ∃ used, used ≤ 5 * bits.length + 3 ∧
      RunsFor program (state 3 other erased bits)
        (finish other (erased + bits.length) (bits.all (!·))) used := by
  induction bits generalizing erased with
  | nil => exact ⟨3, by simp, by simpa using good_empty other erased⟩
  | cons bit rest ih =>
      cases bit with
      | false =>
          obtain ⟨used, hUsed, run⟩ := ih (erased + 1)
          refine ⟨4 + used, by simp; omega, ?_⟩
          simpa [List.all_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (good_false other erased rest).trans run
      | true =>
          obtain ⟨used, hUsed, run⟩ := bad_runs other (erased + 1) rest
          refine ⟨5 + used, by simp; omega, ?_⟩
          simpa [List.all_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (good_true other erased rest).trans run

/-- From a canonical result tape, the finite code consumes every bit and
leaves only the one-bit answer. Its run is independent of the other tape. -/
theorem runs (bits : List Bool) (other : Tape) :
    ∃ finish used,
      used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := other, outputTape := Tape.ofBits bits } : Configuration)
        finish used ∧
      finish.halted = true ∧ finish.inputTape = other ∧
      finish.outputBits = [accepts bits] := by
  cases bits with
  | nil =>
      let start := state 0 other 0 []
      let selected : Configuration := { start with pc := 10 }
      have first : Step program start selected := by
        simp [Step, successors, next, program, start, selected, state,
          Instruction.next, Configuration.tape, Tape.ofBits]
      obtain ⟨used, hUsed, run⟩ := bad_runs other 0 []
      refine ⟨finish other 0 false, 1 + used, ?_, ?_, rfl, rfl, ?_⟩
      · simp [budget] at hUsed ⊢
        omega
      · simpa [start, selected, state, Tape.ofBits] using
          ((RunsFor.zero _).succ first).trans run
      · simp [accepts, BinaryIsOne.accepts, finish_output]
  | cons bit rest =>
      cases bit with
      | false =>
          let start := state 0 other 0 (false :: rest)
          let selected : Configuration := { start with pc := 10 }
          have first : Step program start selected := by
            simp [Step, successors, next, program, start, selected, state,
              Instruction.next, Configuration.tape, Tape.ofBits]
          obtain ⟨used, hUsed, run⟩ := bad_runs other 0 (false :: rest)
          refine ⟨finish other (false :: rest).length false,
            1 + used, ?_, ?_, rfl, rfl, ?_⟩
          · simp [budget] at hUsed ⊢
            omega
          · simpa [start, selected, state, Tape.ofBits] using
              ((RunsFor.zero _).succ first).trans run
          · simp [accepts, BinaryIsOne.accepts, finish_output]
      | true =>
          let start := state 0 other 0 (true :: rest)
          let selected : Configuration := { start with pc := 1 }
          let cleared : Configuration :=
            { selected with pc := 2, outputTape := selected.outputTape.write none }
          let moved : Configuration :=
            { cleared with pc := 3, outputTape := cleared.outputTape.moveRight }
          have first : Step program start selected := by
            simp [Step, successors, next, program, start, selected, state,
              Instruction.next, Configuration.tape, Tape.ofBits]
          have erase : Step program selected cleared := by
            simp [Step, successors, next, program, start, selected, cleared, state,
              Instruction.next, Configuration.updateTape, Configuration.advance]
          have move : Step program cleared moved := by
            simp [Step, successors, next, program, start, selected, cleared, moved, state,
              Instruction.next, Configuration.updateTape, Configuration.advance]
          obtain ⟨used, hUsed, run⟩ := good_runs other 1 rest
          refine ⟨finish other (1 + rest.length) (rest.all (!·)),
            3 + used, ?_, ?_, rfl, rfl, ?_⟩
          · simp [budget]; omega
          · have hMove : moved = state 3 other 1 rest := by
              cases rest <;>
                simp [moved, cleared, selected, start, state, Tape.moveRight,
                  Tape.write, Tape.ofBits]
            have continuation : RunsFor program moved
                (finish other (1 + rest.length) (rest.all (!·))) used := by
              simpa only [hMove] using run
            simpa [start, state, Tape.ofBits] using
              ((((RunsFor.zero _).succ first).succ erase).succ move).trans continuation
          · simpa [accepts, BinaryIsOne.accepts] using
              finish_output other (1 + rest.length) (rest.all (!·))

/-- This routine is intentionally a contextual tape operation: its input
bitstring is already on the output tape, not reloaded for free. -/
theorem runs_from_equivalent (bits : List Bool) (other output : Tape)
    (hOutput : output.Equivalent (Tape.ofBits bits)) :
    ∃ finish used,
      used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := other, outputTape := output } : Configuration)
        finish used ∧
      finish.halted = true ∧ finish.outputBits = [accepts bits] := by
  obtain ⟨target, used, hUsed, run, hHalt, _, hBits⟩ := runs bits other
  obtain ⟨finish, actualRun, hEq⟩ :=
    RunsFor.exists_equivalent (other :=
      { inputTape := other, outputTape := output }) run
    ⟨rfl, rfl, Tape.Equivalent.refl _, hOutput.symm⟩
  exact ⟨finish, used, hUsed, actualRun,
    hEq.2.1.symm.trans hHalt, (hEq.2.2.2.symm.bits).trans hBits⟩

/-- The contextual evaluator agrees with the one test at the charged bound,
even if the result tape contains redundant represented blank cells. -/
theorem eval_from_equivalent (bits : List Bool) (other output : Tape)
    (hOutput : output.Equivalent (Tape.ofBits bits)) :
    (evalConfigWithin program
      ({ inputTape := other, outputTape := output } : Configuration)
      (budget bits.length)).map
        (fun c => if c.halted then some c.outputBits else none) =
      PMF.pure (some [accepts bits]) := by
  obtain ⟨finish, used, hUsed, run, hHalt, hBits⟩ :=
    runs_from_equivalent bits other output hOutput
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hBits]

end Machine.BinaryIsOneInPlace
