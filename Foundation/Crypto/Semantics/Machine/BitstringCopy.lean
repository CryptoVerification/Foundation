import Foundation.Crypto.Semantics.Machine.PolynomialTime

namespace Machine

/-- Copy a contiguous input bitstring onto an initially blank output tape,
one cell at a time. Input and output heads end just past the copied strings.
There is no whole-string primitive, and no randomness is used by this code.
This standalone routine does not reset arbitrary dirty caller tapes. -/
def copyBitstring : Program :=
  [.branch .input 7 1 3,
   .write .output false, .jump 4,
   .write .output true,
   .moveRight .input, .moveRight .output, .jump 0,
   .halt]

private def copyState (copied remaining : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := copied.reverse.map some },
    outputTape := { left := copied.reverse.map some } }

private def copyFinish (bits : List Bool) : Configuration :=
  { copyState bits [] with pc := 7, halted := true }

private def copyBitSteps (b : Bool) : Nat := if b then 5 else 6

/-- Exact transition count of this routine. Zero bits take two transitions:
the blank branch, followed by the explicit halt. -/
def copyBitstringSteps : List Bool → Nat
  | [] => 2
  | b :: rest => copyBitSteps b + copyBitstringSteps rest

private theorem copy_one_bit (copied rest : List Bool) (b : Bool) :
    RunsFor copyBitstring (copyState copied (b :: rest))
      (copyState (copied ++ [b]) rest) (copyBitSteps b) := by
  let start := copyState copied (b :: rest)
  let selected : Configuration := { start with pc := if b then 3 else 1 }
  let written : Configuration :=
    { start with
      pc := if b then 4 else 2
      outputTape := start.outputTape.write (some b) }
  let ready : Configuration := { written with pc := 4 }
  let movedInput : Configuration :=
    { ready with pc := 5, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 6, outputTape := movedInput.outputTape.moveRight }
  have hSelect : Step copyBitstring start selected := by
    cases b <;> simp [Step, successors, next, copyBitstring, start,
      selected, copyState, Tape.ofBits, Instruction.next, Configuration.tape]
  have hWrite : Step copyBitstring selected written := by
    cases b <;> simp [Step, successors, next, copyBitstring, selected,
      written, start, copyState, Tape.ofBits, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hMoveInput : Step copyBitstring ready movedInput := by
    simp [Step, successors, next, copyBitstring, ready, movedInput,
      written, start, copyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hMoveOutput : Step copyBitstring movedInput movedOutput := by
    simp [Step, successors, next, copyBitstring, movedInput, movedOutput,
      ready, written, start, copyState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step copyBitstring movedOutput
      (copyState (copied ++ [b]) rest) := by
    cases rest <;> simp [Step, successors, next, copyBitstring, movedOutput,
      movedInput, ready, written, start, copyState, Instruction.next,
      Tape.ofBits, Tape.moveRight, Tape.write, List.reverse_append]
  cases b with
  | false =>
      have hJump : Step copyBitstring written ready := by
        simp [Step, successors, next, copyBitstring, written, ready,
          start, copyState, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hSelect) hWrite)
          hJump) hMoveInput) hMoveOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hMoveInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite)
          hMoveInput) hMoveOutput) hBack

private theorem copy_run (copied remaining : List Bool) :
    RunsFor copyBitstring (copyState copied remaining)
      (copyFinish (copied ++ remaining)) (copyBitstringSteps remaining) := by
  induction remaining generalizing copied with
  | nil =>
      have hBranch : Step copyBitstring (copyState copied [])
          { copyState copied [] with pc := 7 } := by
        simp [Step, successors, next, copyBitstring, copyState,
          Tape.ofBits, Instruction.next, Configuration.tape]
      have hHalt : Step copyBitstring
          ({ copyState copied [] with pc := 7 } : Configuration)
          (copyFinish copied) := by
        simp [Step, successors, next, copyBitstring, copyState,
          copyFinish, Instruction.next]
      simpa [copyBitstringSteps] using
        RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt
  | cons b rest ih =>
      simpa [copyBitstringSteps, List.append_assoc] using
        (copy_one_bit copied rest b).trans (ih (copied ++ [b]))

theorem copyBitstringSteps_le (input : List Bool) :
    copyBitstringSteps input ≤ 6 * input.length + 2 := by
  induction input with
  | nil => simp [copyBitstringSteps]
  | cons b rest ih =>
      cases b <;> simp only [copyBitstringSteps, copyBitSteps,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- Exact tape state at the end of copying. Both heads are just past the
contiguous bitstrings. Keeping the tape state explicit allows a caller to
compose subsequent head-positioning routines without a free reset. -/
def copyBitstringFinish (input : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { left := input.reverse.map some },
    outputTape := { left := input.reverse.map some },
    halted := true }

theorem copyBitstring_runs (input : List Bool) :
    RunsFor copyBitstring (Configuration.initial input)
      (copyBitstringFinish input) (copyBitstringSteps input) := by
  have hInitial : copyState [] input = Configuration.initial input := by
    cases input <;> rfl
  have run := copy_run [] input
  rw [hInitial] at run
  simpa [copyFinish, copyState, copyBitstringFinish, Tape.ofBits] using run

theorem copyBitstring_haltsWith (input : List Bool) :
    HaltsWith copyBitstring input input (copyBitstringSteps input) := by
  refine ⟨copyBitstringFinish input, copyBitstring_runs input, rfl, ?_⟩
  simp [copyBitstringFinish, Configuration.outputBits, Tape.bits]

theorem copyBitstring_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyBitstring := by
  simp [copyBitstring]

theorem copyBitstring_eval_exact (input : List Bool) :
    evalWithin copyBitstring input (copyBitstringSteps input) =
      PMF.pure (some input) := by
  exact (copyBitstring_haltsWith input).evalWithin_eq_pure_of_no_randomBit
    copyBitstring_no_randomBit

theorem copyBitstring_haltsWithin_exact (input : List Bool) :
    HaltsWithin copyBitstring input (copyBitstringSteps input) := by
  exact (copyBitstring_haltsWith input).haltsWithin_of_no_randomBit
    copyBitstring_no_randomBit

theorem copyBitstring_haltsWithin (input : List Bool) :
    HaltsWithin copyBitstring input (6 * input.length + 2) :=
  (copyBitstring_haltsWithin_exact input).mono (copyBitstringSteps_le input)

theorem copyBitstring_eval (input : List Bool) :
    evalWithin copyBitstring input (6 * input.length + 2) =
      PMF.pure (some input) := by
  rw [evalWithin_eq_of_haltsWithin copyBitstring input
    (6 * input.length + 2) (copyBitstringSteps input)
    (copyBitstring_haltsWithin input) (copyBitstring_haltsWithin_exact input)]
  exact copyBitstring_eval_exact input

/-- A linear worst-case bound in total input bit length, with correctness
proved from actual one-cell machine transitions. -/
theorem copyBitstring_polynomialTime : PolynomialTime copyBitstring := by
  refine ⟨fun m => 6 * m + 2, ?_, copyBitstring_haltsWithin⟩
  exact ((PolynomiallyBounded.const 6).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 2)

private theorem copyBitstring_blank_run (input output : Tape) (hBlank : input.current = none) :
    RunsFor copyBitstring ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 7, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  have hBranch : Step copyBitstring start { start with pc := 7 } := by
    simp [Step, successors, next, copyBitstring, start, Instruction.next, Configuration.tape, hBlank]
  have hHalt : Step copyBitstring ({ start with pc := 7 } : Configuration)
      { start with pc := 7, halted := true } := by
    simp [Step, successors, next, copyBitstring, start, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt

private theorem copyBitstring_cell_run (input output : Tape) (bit : Bool)
    (hBit : input.current = some bit) :
    RunsFor copyBitstring ({ inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight, outputTape := (output.write (some bit)).moveRight } : Configuration)
      (if bit then 5 else 6) := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := if bit then 3 else 1 }
  let written : Configuration := { start with pc := if bit then 4 else 2, outputTape := output.write (some bit) }
  let ready : Configuration := { written with pc := 4 }
  let movedInput : Configuration := { ready with pc := 5, inputTape := input.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 6, outputTape := (output.write (some bit)).moveRight }
  have hSelect : Step copyBitstring start selected := by
    cases bit <;> simp [Step, successors, next, copyBitstring, start, selected,
      Instruction.next, Configuration.tape, hBit]
  have hWrite : Step copyBitstring selected written := by
    cases bit <;> simp [Step, successors, next, copyBitstring, selected, written, start,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step copyBitstring ready movedInput := by
    simp [Step, successors, next, copyBitstring, ready, written, start, movedInput,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step copyBitstring movedInput movedOutput := by
    simp [Step, successors, next, copyBitstring, ready, written, start, movedInput, movedOutput,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step copyBitstring movedOutput
      ({ inputTape := input.moveRight, outputTape := (output.write (some bit)).moveRight } : Configuration) := by
    simp [Step, successors, next, copyBitstring, ready, written, start, movedInput, movedOutput, Instruction.next]
  cases bit with
  | false =>
      have hJump : Step copyBitstring written ready := by
        simp [Step, successors, next, copyBitstring, written, ready, start, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := rfl
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hInput) hOutput) hBack

private theorem copyBitstring_fresh_move (before : List (Option Bool)) (blanks : Nat) (bit : Bool) :
    (({ left := before, right := List.replicate blanks none } : Tape).write (some bit)).moveRight =
      { left := some bit :: before, right := List.replicate (blanks - 1) none } := by
  cases blanks <;> simp [Tape.write, Tape.moveRight, List.replicate_succ]

private theorem copyBitstring_finite_run (left right : List (Option Bool))
    (current : Option Bool) (output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 6 * (right.length + 1) + 2 ∧
      RunsFor copyBitstring
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.inputTape = (Tape.moveRight^[((current :: right).takeWhile Option.isSome).length])
        { left := left, current := current, right := right } ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ (bits : List Bool) (remaining : Nat),
          finish.outputTape =
            { left := bits.reverse.map some ++ before, right := List.replicate remaining none } := by
  induction right generalizing left current output with
  | nil =>
      cases current with
      | none =>
          refine ⟨_, 2, by simp, copyBitstring_blank_run _ output rfl, rfl, rfl, rfl, ?_⟩
          intro before blanks hOutput
          exact ⟨[], blanks, hOutput⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit }
          have hBit := copyBitstring_cell_run input output bit rfl
          have hBlank := copyBitstring_blank_run input.moveRight (output.write (some bit)).moveRight rfl
          refine ⟨_, (if bit then 5 else 6) + 2, ?_, hBit.trans hBlank, rfl, rfl, rfl, ?_⟩
          · cases bit <;> decide
          · intro before blanks hOutput
            exact ⟨[bit], blanks - 1, by
              change (output.write (some bit)).moveRight = _
              rw [hOutput, copyBitstring_fresh_move]
              simp⟩
  | cons cell rest ih =>
      cases current with
      | none =>
          refine ⟨_, 2, by simp, copyBitstring_blank_run _ output rfl, rfl, rfl, rfl, ?_⟩
          intro before blanks hOutput
          exact ⟨[], blanks, hOutput⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit, right := cell :: rest }
          obtain ⟨finish, used, hBound, hRun, hHalted, hInputBlank, hInput, hLayout⟩ :=
            ih (some bit :: left) cell (output.write (some bit)).moveRight
          have hBit := copyBitstring_cell_run input output bit rfl
          change RunsFor copyBitstring
            ({ inputTape := input.moveRight, outputTape := (output.write (some bit)).moveRight } : Configuration)
            finish used at hRun
          refine ⟨finish, (if bit then 5 else 6) + used, ?_, hBit.trans hRun,
            hHalted, hInputBlank, ?_, ?_⟩
          · cases bit <;> simp only [List.length_cons, Bool.false_eq_true, ↓reduceIte] <;> omega
          · simpa only [List.takeWhile, Option.isSome_some, Bool.true_eq_false,
              ↓reduceIte, List.length_cons, Function.iterate_succ_apply, input, Tape.moveRight] using hInput
          · intro before blanks hOutput
            obtain ⟨bits, remaining, hFinish⟩ := hLayout (some bit :: before) (blanks - 1)
              (by rw [hOutput, copyBitstring_fresh_move])
            refine ⟨bit :: bits, remaining, ?_⟩
            simpa [List.reverse_cons, List.map_append, List.append_assoc] using hFinish

/-- Linear stopping bound on arbitrary finite tapes, including internal
blanks and dirty output cells. The scan stops at the first input blank.
This runtime assertion does not promise that arbitrary saved output data
are preserved, or interpret a malformed input as a successful field. -/
theorem copyBitstring_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 6 * input.cells + 2 ∧
      RunsFor copyBitstring ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, hRun, hHalted, _hInputBlank, _hInput, _hLayout⟩ :=
    copyBitstring_finite_run input.left input.right input.current output
  refine ⟨finish, used, ?_, hRun, hHalted⟩
  dsimp only [Tape.cells]
  omega

/-- The source head stops at its first blank after exactly the displayed
number of one-cell moves. In particular, a halted copy retains the cells
after that blank. This applies to dirty destinations and malformed fields;
the list expression describes native movement rather than a tape reset. -/
theorem copyBitstring_halted_input_layout (input output : Tape)
    (finish : Configuration) (used : Nat)
    (run : RunsFor copyBitstring
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    finish.inputTape =
      (Tape.moveRight^[((input.current :: input.right).takeWhile Option.isSome).length]) input ∧
      finish.inputTape.current = none := by
  obtain ⟨target, targetTime, _hBound, targetRun, targetHalt, targetBlank, targetInput, _hLayout⟩ :=
    copyBitstring_finite_run input.left input.right input.current output
  have hFinish := run.halted_finish_eq_of_no_randomBit targetRun
    hHalted targetHalt copyBitstring_no_randomBit
  rw [hFinish]
  exact ⟨targetInput, targetBlank⟩

/-- Contiguous copying appends one finite bit block to the caller's saved
output cells, including when that block is empty. The actual source head
stops on a blank; the destination retains its blank right frontier. -/
theorem copyBitstring_terminates_with_retained_output (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ (finish : Configuration) (used : Nat) (bits : List Bool) (remaining : Nat),
      used ≤ 6 * input.cells + 2 ∧
      RunsFor copyBitstring
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.outputTape =
        { left := bits.reverse.map some ++ before, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hInputBlank, _hInput, hLayout⟩ :=
    copyBitstring_finite_run input.left input.right input.current
      { left := before, right := List.replicate blanks none }
  obtain ⟨bits, remaining, hOutput⟩ := hLayout before blanks rfl
  refine ⟨finish, used, bits, remaining, ?_, run, hHalted, hInputBlank, hOutput⟩
  dsimp only [Tape.cells]
  omega

/-- Contiguous copying on arbitrary finite input tapes preserves a fresh
output frontier. An internal input blank ends the actual scan without
requiring a valid protocol field or silently discarding caller storage. -/
theorem copyBitstring_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining, used ≤ 6 * input.cells + 2 ∧
      RunsFor copyBitstring
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, bits, remaining, hBound, run, hHalted, _hInputBlank, hOutput⟩ :=
    copyBitstring_terminates_with_retained_output input before blanks
  exact ⟨finish, used, bits.reverse.map some ++ before, remaining, hBound, run, hHalted, hOutput⟩

end Machine
