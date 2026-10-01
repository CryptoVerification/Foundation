import Foundation.Machine.UnaryInput
import Foundation.Machine.FramedInput
import Foundation.Machine.GuardedOutput

namespace Machine

private theorem skipUnary_step_input_moveRight (c d : Configuration) (step : Step skipUnary c d) :
    d.inputTape = c.inputTape ∨ d.inputTape = c.inputTape.moveRight := by
  have hActive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) step)
  by_cases hPc : c.pc < 6
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, skipUnary,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : skipUnary[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 6 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

private theorem skipFrame_step_input_moveRight (c d : Configuration) (step : Step skipFrame c d) :
    d.inputTape = c.inputTape ∨ d.inputTape = c.inputTape.moveRight := by
  have hActive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) step)
  by_cases hPc : c.pc < 13
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, skipFrame,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : skipFrame[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 13 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

/-- The unary scanner only advances the input head; retained cells to its
right are an actual suffix of the original cells, including internal blanks. -/
theorem skipUnary_input_right_suffix {start finish : Configuration} {used : Nat}
    (run : RunsFor skipUnary start finish used) :
    ∃ count, finish.inputTape.right = start.inputTape.right.drop count :=
  run.input_right_suffix_of_step (fun c d step => by
    rcases skipUnary_step_input_moveRight c d step with hSame | hRight
    · exact Or.inl (congrArg Tape.right hSame)
    · apply Or.inr
      rw [hRight]
      cases hCells : c.inputTape.right <;> simp [Tape.moveRight, hCells])

/-- Frame scanning may consume a truncated payload past a separator, but
does not write or move left on the input tape. This tracks its exact suffix. -/
theorem skipFrame_input_right_suffix {start finish : Configuration} {used : Nat}
    (run : RunsFor skipFrame start finish used) :
    ∃ count, finish.inputTape.right = start.inputTape.right.drop count :=
  run.input_right_suffix_of_step (fun c d step => by
    rcases skipFrame_step_input_moveRight c d step with hSame | hRight
    · exact Or.inl (congrArg Tape.right hSame)
    · apply Or.inr
      rw [hRight]
      cases hCells : c.inputTape.right <;> simp [Tape.moveRight, hCells])

/-- The unary reader advances the whole retained input tape by actual
one-cell moves. The number of moves is bounded by the charged trace length. -/
theorem skipUnary_input_moveRight {start finish : Configuration} {used : Nat}
    (run : RunsFor skipUnary start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape :=
  run.input_moveRight_of_step skipUnary_step_input_moveRight

/-- The frame reader may cross separators on malformed data, but its input
head still only moves right. Saved input cells are never replaced. -/
theorem skipFrame_input_moveRight {start finish : Configuration} {used : Nat}
    (run : RunsFor skipFrame start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape :=
  run.input_moveRight_of_step skipFrame_step_input_moveRight

/-- Physical layout fixture only: caller data can follow a frame through
blank separators. No instruction loads or normalizes this whole list. -/
private def tapeAtCells (before cells : List (Option Bool)) : Tape :=
  match cells with
  | [] => { left := before }
  | cell :: rest => { left := before, current := cell, right := rest }

/-- A unary header on a tape which may contain protected data beyond a
later separator. Unlike a fresh-input fixture, the following cells need
not form a contiguous bitstring. The output tape is arbitrary. -/
def skipUnaryCellsStart (before : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := tapeAtCells before (List.replicate count (some true) ++ some false :: rest),
    outputTape := output }

def skipUnaryCellsFinish (before : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 2,
    inputTape := tapeAtCells (some false :: (List.replicate count (some true) ++ before)) rest,
    outputTape := output, halted := true }

/-- Same six native instructions and the same exact transition count. The
scan stops after its false delimiter, not at an arbitrary later blank. -/
theorem skipUnaryCells_runs (before : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (output : Tape) :
    RunsFor skipUnary (skipUnaryCellsStart before count rest output)
      (skipUnaryCellsFinish before count rest output) (3 * count + 3) := by
  induction count generalizing before with
  | zero =>
      let start := skipUnaryCellsStart before 0 rest output
      let selected : Configuration := { start with pc := 1 }
      let moved : Configuration := { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, skipUnaryCellsStart,
          tapeAtCells, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected moved := by
        simp [Step, successors, next, skipUnary, start, selected, moved, skipUnaryCellsStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipUnary moved (skipUnaryCellsFinish before 0 rest output) := by
        cases rest <;> simp [Step, successors, next, skipUnary, start, selected, moved,
          skipUnaryCellsStart, skipUnaryCellsFinish, tapeAtCells, Tape.moveRight, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | succ count ih =>
      let start := skipUnaryCellsStart before (count + 1) rest output
      let selected : Configuration := { start with pc := 3 }
      let moved : Configuration := { selected with pc := 4, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, skipUnaryCellsStart,
          tapeAtCells, List.replicate_succ, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected moved := by
        simp [Step, successors, next, skipUnary, start, selected, moved, skipUnaryCellsStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipUnary moved (skipUnaryCellsStart (some true :: before) count rest output) := by
        cases count <;> simp [Step, successors, next, skipUnary, start, selected, moved,
          skipUnaryCellsStart, tapeAtCells, List.replicate_succ, Tape.moveRight, Instruction.next]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2).trans
        (ih (some true :: before))
      have hFinish : skipUnaryCellsFinish (some true :: before) count rest output =
          skipUnaryCellsFinish before (count + 1) rest output := by
        simp [skipUnaryCellsFinish, List.replicate_succ', List.append_assoc]
      rw [hFinish] at run
      convert run using 1
      omega

theorem skipUnaryCells_eval (before : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (output : Tape) :
    evalConfigWithin skipUnary (skipUnaryCellsStart before count rest output) (3 * count + 3) =
      PMF.pure (skipUnaryCellsFinish before count rest output) :=
  (skipUnaryCells_runs before count rest output).evalConfigWithin_eq_pure_of_no_randomBit
    skipUnary_no_randomBit

private def advanceCells (tape : Tape) : Nat → Tape
  | 0 => tape
  | count + 1 => advanceCells tape.moveRight count

private def contextualCounter (saved : List (Option Bool)) : Nat → List (Option Bool) → Tape
  | 0, right => { left := saved, right := right }
  | count + 1, right =>
      { left := List.replicate count (some true) ++ none :: saved, current := some true, right := right }

private def contextConsumeStart (saved : List (Option Bool)) (count : Nat)
    (right : List (Option Bool)) (input : Tape) : Configuration :=
  { pc := 7, inputTape := input, outputTape := contextualCounter saved count right }

private def contextConsumeFinish (saved : List (Option Bool)) (count : Nat)
    (right : List (Option Bool)) (input : Tape) : Configuration :=
  { pc := 12, inputTape := advanceCells input count,
    outputTape := { left := saved, right := List.replicate count none ++ right }, halted := true }

private theorem contextConsume_runs (saved : List (Option Bool)) (count : Nat)
    (right : List (Option Bool)) (input : Tape) :
    RunsFor skipFrame (contextConsumeStart saved count right input)
      (contextConsumeFinish saved count right input) (5 * count + 2) := by
  induction count generalizing right input with
  | zero =>
      let start := contextConsumeStart saved 0 right input
      let selected : Configuration := { start with pc := 12 }
      have h0 : Step skipFrame start selected := by
        simp [Step, successors, next, skipFrame, start, selected, contextConsumeStart,
          contextualCounter, Instruction.next, Configuration.tape]
      have h1 : Step skipFrame selected (contextConsumeFinish saved 0 right input) := by
        simp [Step, successors, next, skipFrame, start, selected, contextConsumeStart,
          contextConsumeFinish, contextualCounter, advanceCells, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | succ count ih =>
      let start := contextConsumeStart saved (count + 1) right input
      let selected : Configuration := { start with pc := 8 }
      let erased : Configuration := { selected with pc := 9, outputTape := selected.outputTape.write none }
      let movedInput : Configuration := { erased with pc := 10, inputTape := input.moveRight }
      let movedOutput : Configuration := { movedInput with pc := 11, outputTape := movedInput.outputTape.moveLeft }
      have h0 : Step skipFrame start selected := by
        simp [Step, successors, next, skipFrame, start, selected, contextConsumeStart,
          contextualCounter, Instruction.next, Configuration.tape]
      have h1 : Step skipFrame selected erased := by
        simp [Step, successors, next, skipFrame, start, selected, erased, contextConsumeStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipFrame erased movedInput := by
        simp [Step, successors, next, skipFrame, start, selected, erased, movedInput,
          contextConsumeStart, contextualCounter, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have h3 : Step skipFrame movedInput movedOutput := by
        simp [Step, successors, next, skipFrame, movedInput, movedOutput, start, selected, erased, contextConsumeStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h4 : Step skipFrame movedOutput (contextConsumeStart saved count (none :: right) input.moveRight) := by
        cases count <;> simp [Step, successors, next, skipFrame, start, selected, erased,
          movedInput, movedOutput, contextConsumeStart, contextualCounter,
          Instruction.next, Tape.moveLeft, Tape.write, List.replicate_succ]
      have hFinish : contextConsumeFinish saved count (none :: right) input.moveRight =
          contextConsumeFinish saved (count + 1) right input := by
        simp [contextConsumeFinish, advanceCells, List.replicate_succ', List.append_assoc]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4).trans (ih (none :: right) input.moveRight)
      rw [hFinish] at run
      convert run using 1
      omega

private def contextFrameReader (before saved : List (Option Bool))
    (copied : Nat) (rest : List (Option Bool)) (blanks : Nat := 0) : Configuration :=
  { inputTape := tapeAtCells (List.replicate copied (some true) ++ before) rest,
    outputTape := {
      left := List.replicate copied (some true) ++ none :: saved
      right := List.replicate (blanks - copied) none } }

private theorem contextFrame_bit (before saved : List (Option Bool))
    (copied : Nat) (rest : List (Option Bool)) (blanks : Nat := 0) :
    RunsFor skipFrame (contextFrameReader before saved copied (some true :: rest) blanks)
      (contextFrameReader before saved (copied + 1) rest blanks) 5 := by
  let start := contextFrameReader before saved copied (some true :: rest) blanks
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration := { selected with pc := 2, outputTape := selected.outputTape.write (some true) }
  let movedInput : Configuration := { written with pc := 3, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have h0 : Step skipFrame start selected := by
    simp [Step, successors, next, skipFrame, start, selected, contextFrameReader,
      tapeAtCells, Instruction.next, Configuration.tape]
  have h1 : Step skipFrame selected written := by
    simp [Step, successors, next, skipFrame, selected, written, start, contextFrameReader,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step skipFrame written movedInput := by
    simp [Step, successors, next, skipFrame, written, movedInput, start, selected, contextFrameReader,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step skipFrame movedInput movedOutput := by
    simp [Step, successors, next, skipFrame, movedInput, movedOutput, start, selected, written, contextFrameReader,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step skipFrame movedOutput (contextFrameReader before saved (copied + 1) rest blanks) := by
    have hSub : blanks - (copied + 1) = (blanks - copied) - 1 := by omega
    cases hPad : blanks - copied <;> cases rest <;>
      simp [Step, successors, next, skipFrame, start, selected, written,
        movedInput, movedOutput, contextFrameReader, tapeAtCells, Instruction.next,
        Tape.moveRight, Tape.write, List.replicate_succ, hSub, hPad]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem contextFrame_read (before saved : List (Option Bool))
    (remaining copied : Nat) (rest : List (Option Bool)) (blanks : Nat := 0) :
    RunsFor skipFrame
      (contextFrameReader before saved copied (List.replicate remaining (some true) ++ some false :: rest) blanks)
      (contextConsumeStart saved (copied + remaining) (none :: List.replicate (blanks - (copied + remaining)) none)
        (tapeAtCells (some false :: (List.replicate (copied + remaining) (some true) ++ before)) rest))
      (5 * remaining + 3) := by
  induction remaining generalizing copied with
  | zero =>
      let start := contextFrameReader before saved copied (some false :: rest) blanks
      let selected : Configuration := { start with pc := 5 }
      let moved : Configuration := { selected with pc := 6, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipFrame start selected := by
        simp [Step, successors, next, skipFrame, start, selected, contextFrameReader,
          tapeAtCells, Instruction.next, Configuration.tape]
      have h1 : Step skipFrame selected moved := by
        simp [Step, successors, next, skipFrame, selected, moved, start, contextFrameReader,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipFrame moved
          (contextConsumeStart saved copied (none :: List.replicate (blanks - copied) none)
            (tapeAtCells (some false :: (List.replicate copied (some true) ++ before)) rest)) := by
        cases copied <;> cases rest <;> simp [Step, successors, next, skipFrame, start,
          selected, moved, contextFrameReader, contextConsumeStart, contextualCounter,
          tapeAtCells, Instruction.next, Configuration.updateTape, Configuration.advance,
          Tape.moveRight, Tape.moveLeft, List.replicate_succ]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | succ remaining ih =>
      have run := (contextFrame_bit before saved copied
        (List.replicate remaining (some true) ++ some false :: rest) blanks).trans (ih (copied + 1))
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run

/-- Invoke the same thirteen native frame-scanning instructions with
explicit blank padding after the fresh output head. Erased counter cells and
unused pre-existing padding both remain in the returned finite tape. -/
def skipFrameCellsPaddedStart (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (blanks : Nat) : Configuration :=
  { inputTape := tapeAtCells beforeInput (List.replicate count (some true) ++ some false :: rest),
    outputTape := { left := none :: savedOutput, right := List.replicate blanks none } }

def skipFrameCellsPaddedFinish (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (blanks : Nat) : Configuration :=
  { pc := 12,
    inputTape := advanceCells
      (tapeAtCells (some false :: (List.replicate count (some true) ++ beforeInput)) rest) count,
    outputTape := {
      left := savedOutput
      right := List.replicate (count + 1 + (blanks - count)) none }, halted := true }

theorem skipFrameCellsPadded_runs (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (blanks : Nat) :
    RunsFor skipFrame (skipFrameCellsPaddedStart beforeInput savedOutput count rest blanks)
      (skipFrameCellsPaddedFinish beforeInput savedOutput count rest blanks) (10*count + 5) := by
  have reader := contextFrame_read beforeInput savedOutput count 0 rest blanks
  simp only [Nat.zero_add] at reader
  have run := reader.trans (contextConsume_runs savedOutput count
    (none :: List.replicate (blanks - count) none)
    (tapeAtCells (some false :: (List.replicate count (some true) ++ beforeInput)) rest))
  have hCount : 5*count + 3 + (5*count + 2) = 10*count + 5 := by omega
  rw [hCount] at run
  simpa [contextFrameReader, skipFrameCellsPaddedStart, skipFrameCellsPaddedFinish,
    contextConsumeFinish, List.replicate_succ', List.replicate_add, List.append_assoc,
    Nat.add_assoc] using run

private theorem contextFrame_unterminated (before saved : List (Option Bool))
    (remaining copied : Nat) (tail : List (Option Bool)) (blanks : Nat)
    (hBlank : (tapeAtCells [] tail).current = none) :
    RunsFor skipFrame
      (contextFrameReader before saved copied (List.replicate remaining (some true) ++ tail) blanks)
      ({ contextFrameReader before saved (copied + remaining) tail blanks with
         pc := 12, halted := true } : Configuration) (5 * remaining + 2) := by
  induction remaining generalizing copied with
  | zero =>
      have hCurrent : (tapeAtCells (List.replicate copied (some true) ++ before) tail).current = none := by
        cases tail with
        | nil => rfl
        | cons cell rest => simpa only [tapeAtCells] using hBlank
      let start := contextFrameReader before saved copied tail blanks
      have h0 : Step skipFrame start { start with pc := 12 } := by
        simp [Step, successors, next, skipFrame, start, contextFrameReader,
          Instruction.next, Configuration.tape, hCurrent]
      have h1 : Step skipFrame ({ start with pc := 12 } : Configuration)
          { start with pc := 12, halted := true } := by
        simp [Step, successors, next, skipFrame, start, contextFrameReader, Instruction.next]
      simpa only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
        RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | succ remaining ih =>
      have run := (contextFrame_bit before saved copied
        (List.replicate remaining (some true) ++ tail) blanks).trans (ih (copied + 1))
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run

private theorem contextualUnary_split (cells : List (Option Bool)) :
    ∃ count tail, cells = List.replicate count (some true) ++ tail ∧
      ((tapeAtCells [] tail).current = none ∨ ∃ rest, tail = some false :: rest) := by
  induction cells with
  | nil => exact ⟨0, [], rfl, Or.inl rfl⟩
  | cons cell rest ih =>
      cases cell with
      | none => exact ⟨0, none :: rest, rfl, Or.inl rfl⟩
      | some bit =>
          cases bit with
          | false => exact ⟨0, some false :: rest, rfl, Or.inr ⟨rest, rfl⟩⟩
          | true =>
              obtain ⟨count, tail, hCells, hEnd⟩ := ih
              exact ⟨count + 1, tail, by simp [List.replicate_succ, hCells], hEnd⟩

/-- Frame scanning with a reserved blank before the output counter stops
on arbitrary finite input cells, including missing terminators and payloads
which cross internal blanks. Saved output cells are protected by that
separator, and the returned output has a fresh blank frontier. -/
theorem skipFrameCells_terminates_with_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 10 * input.cells + 5 ∧
      RunsFor skipFrame
        ({ inputTape := input,
           outputTape := { left := none :: savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } := by
  obtain ⟨count, tail, hCells, hEnd⟩ := contextualUnary_split (input.current :: input.right)
  have hCount : count ≤ input.right.length + 1 := by
    have hLength := congrArg List.length hCells
    simp only [List.length_cons, List.length_append, List.length_replicate] at hLength
    omega
  have hTape : input = tapeAtCells input.left (List.replicate count (some true) ++ tail) := by
    rw [← hCells]
    rfl
  rcases hEnd with hBlank | ⟨rest, rfl⟩
  · have hRun := contextFrame_unterminated input.left savedOutput count 0 tail blanks hBlank
    have hStart : contextFrameReader input.left savedOutput 0
        (List.replicate count (some true) ++ tail) blanks =
        ({ inputTape := input, outputTape := { left := none :: savedOutput, right := List.replicate blanks none } } : Configuration) := by
      simp only [contextFrameReader, List.replicate_zero, List.nil_append, Nat.sub_zero]
      rw [← hTape]
    rw [hStart] at hRun
    refine ⟨_, 5 * count + 2, List.replicate count (some true) ++ none :: savedOutput,
      blanks - count, ?_, hRun, rfl, ?_⟩
    · dsimp only [Tape.cells]; omega
    · simp [contextFrameReader]
  · have hRun := skipFrameCellsPadded_runs input.left savedOutput count rest blanks
    have hStart : skipFrameCellsPaddedStart input.left savedOutput count rest blanks =
        ({ inputTape := input, outputTape := { left := none :: savedOutput, right := List.replicate blanks none } } : Configuration) := by
      simp only [skipFrameCellsPaddedStart]
      rw [← hTape]
    rw [hStart] at hRun
    refine ⟨_, 10 * count + 5, savedOutput, count + 1 + (blanks - count),
      ?_, hRun, rfl, rfl⟩
    dsimp only [Tape.cells]
    omega

theorem skipFrameCellsPaddedStart_layout (beforeInput savedOutput : List (Option Bool))
    (count : Nat) (rest : List (Option Bool)) (blanks : Nat) :
    skipFrameCellsPaddedStart beforeInput savedOutput count rest blanks =
      { inputTape := { ({ right := List.replicate count (some true) ++ some false :: rest } : Tape).moveRight
          with left := beforeInput },
        outputTape := { left := none :: savedOutput, right := List.replicate blanks none } } := by
  cases count <;> simp [skipFrameCellsPaddedStart, tapeAtCells, Tape.moveRight, List.replicate_succ]

/-- A frame boundary in a caller with saved data on both tapes. The output
head has a reserved blank immediately behind it, before `savedOutput`.
The caller must actually allocate that separator with a head movement. -/
def skipFrameCellsStart (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) : Configuration :=
  { inputTape := tapeAtCells beforeInput (List.replicate count (some true) ++ some false :: rest),
    outputTape := { left := none :: savedOutput } }

def skipFrameCellsFinish (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) : Configuration :=
  { pc := 12,
    inputTape := advanceCells
      (tapeAtCells (some false :: (List.replicate count (some true) ++ beforeInput)) rest) count,
    outputTape := { left := savedOutput, right := List.replicate (count + 1) none },
    halted := true }

/-- Reuse the thirteen original frame-scanning instructions. Saved output
data cannot be consumed as counter bits: the explicit blank stops the scan.
Following input cells, including separators and raw responses, survive. -/
theorem skipFrameCells_runs (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) :
    RunsFor skipFrame (skipFrameCellsStart beforeInput savedOutput count rest)
      (skipFrameCellsFinish beforeInput savedOutput count rest) (10 * count + 5) := by
  have reader := contextFrame_read beforeInput savedOutput count 0 rest
  simp only [Nat.zero_add, Nat.zero_sub, List.replicate_zero] at reader
  have run := reader.trans (contextConsume_runs savedOutput count [none]
    (tapeAtCells (some false :: (List.replicate count (some true) ++ beforeInput)) rest))
  have hCount : 5 * count + 3 + (5 * count + 2) = 10 * count + 5 := by omega
  rw [hCount] at run
  simpa [contextFrameReader, skipFrameCellsStart, skipFrameCellsFinish,
    contextConsumeFinish, List.replicate_succ'] using run

private theorem advanceCells_bits (bits : List Bool) (rest before : List (Option Bool)) :
    advanceCells (tapeAtCells before (bits.map some ++ rest)) bits.length =
      tapeAtCells (bits.reverse.map some ++ before) rest := by
  induction bits generalizing before with
  | nil => simp [advanceCells]
  | cons bit bits ih =>
      have hMove : (tapeAtCells before ((bit :: bits).map some ++ rest)).moveRight =
          tapeAtCells (some bit :: before) (bits.map some ++ rest) := by
        cases hCells : bits.map some ++ rest <;> simp [tapeAtCells, Tape.moveRight, hCells]
      simp only [List.length_cons, advanceCells, hMove]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using ih (some bit :: before)

/-- Exact input layout for a valid frame followed by arbitrary caller cells. -/
theorem skipFrameCellsFinish_input (beforeInput savedOutput : List (Option Bool))
    (bits : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    (skipFrameCellsFinish beforeInput savedOutput bits.length (bits.map some ++ current :: right)).inputTape =
      { left := bits.reverse.map some ++ some false ::
          (List.replicate bits.length (some true) ++ beforeInput),
        current := current, right := right } := by
  exact advanceCells_bits bits (current :: right) _

theorem skipFrameCells_eval (beforeInput savedOutput : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) :
    evalConfigWithin skipFrame (skipFrameCellsStart beforeInput savedOutput count rest) (10 * count + 5) =
      PMF.pure (skipFrameCellsFinish beforeInput savedOutput count rest) :=
  (skipFrameCells_runs beforeInput savedOutput count rest).evalConfigWithin_eq_pure_of_no_randomBit
    skipFrame_no_randomBit

theorem skipUnaryCellsStart_layout (before : List (Option Bool)) (count : Nat)
    (rest : List (Option Bool)) (output : Tape) :
    skipUnaryCellsStart before count rest output =
      { inputTape := { ({ right := List.replicate count (some true) ++ some false :: rest } : Tape).moveRight
          with left := before }, outputTape := output } := by
  cases count <;> simp [skipUnaryCellsStart, tapeAtCells, Tape.moveRight, List.replicate_succ]

theorem skipUnaryCellsFinish_layout (before : List (Option Bool)) (count : Nat)
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    skipUnaryCellsFinish before count (current :: right) output =
      { pc := 2,
        inputTape := {
          left := some false :: (List.replicate count (some true) ++ before)
          current := current
          right := right }, outputTape := output, halted := true } := rfl

theorem skipFrameCellsStart_layout (beforeInput savedOutput : List (Option Bool))
    (count : Nat) (rest : List (Option Bool)) :
    skipFrameCellsStart beforeInput savedOutput count rest =
      { inputTape := { ({ right := List.replicate count (some true) ++ some false :: rest } : Tape).moveRight
          with left := beforeInput }, outputTape := { left := none :: savedOutput } } := by
  cases count <;> simp [skipFrameCellsStart, tapeAtCells, Tape.moveRight, List.replicate_succ]

/-- Start the existing native frontier scan on a contiguous segment followed
by a blank separator and arbitrary saved following cells. -/
def seekBitstringNextStart (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := tapeAtCells before (bits.map some ++ none :: rest), outputTape := output }

def seekBitstringNextFinish (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 4,
    inputTape := tapeAtCells (none :: (bits.reverse.map some ++ before)) rest,
    outputTape := output, halted := true }

/-- The blank separator is crossed by an explicit move. Data after it are
not scanned, erased, or silently folded into the preceding segment. -/
theorem seekBitstringNext_runs (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) :
    RunsFor GuardedCompiler.seekScratchInput (seekBitstringNextStart before bits rest output)
      (seekBitstringNextFinish before bits rest output) (3 * bits.length + 3) := by
  induction bits generalizing before with
  | nil =>
      let start := seekBitstringNextStart before [] rest output
      let selected : Configuration := { start with pc := 3 }
      let moved : Configuration := { selected with pc := 4, inputTape := selected.inputTape.moveRight }
      have h0 : Step GuardedCompiler.seekScratchInput start selected := by
        simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected,
          seekBitstringNextStart, tapeAtCells, Instruction.next, Configuration.tape]
      have h1 : Step GuardedCompiler.seekScratchInput selected moved := by
        simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected, moved,
          seekBitstringNextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step GuardedCompiler.seekScratchInput moved (seekBitstringNextFinish before [] rest output) := by
        cases rest <;> simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected, moved,
          seekBitstringNextStart, seekBitstringNextFinish, tapeAtCells, Tape.moveRight, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | cons bit bits ih =>
      let start := seekBitstringNextStart before (bit :: bits) rest output
      let selected : Configuration := { start with pc := 1 }
      let moved : Configuration := { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      have h0 : Step GuardedCompiler.seekScratchInput start selected := by
        cases bit <;> simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected,
          seekBitstringNextStart, tapeAtCells, Instruction.next, Configuration.tape]
      have h1 : Step GuardedCompiler.seekScratchInput selected moved := by
        simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected, moved,
          seekBitstringNextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step GuardedCompiler.seekScratchInput moved (seekBitstringNextStart (some bit :: before) bits rest output) := by
        cases bits <;> simp [Step, successors, next, GuardedCompiler.seekScratchInput, start, selected, moved,
          seekBitstringNextStart, tapeAtCells, Tape.moveRight, Instruction.next]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2).trans
        (ih (some bit :: before))
      have hFinish : seekBitstringNextFinish (some bit :: before) bits rest output =
          seekBitstringNextFinish before (bit :: bits) rest output := by
        simp [seekBitstringNextFinish, List.reverse_cons, List.map_append, List.append_assoc]
      rw [hFinish] at run
      convert run using 1
      simp only [List.length_cons]
      omega

theorem seekBitstringNext_eval (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) :
    evalConfigWithin GuardedCompiler.seekScratchInput (seekBitstringNextStart before bits rest output)
      (3 * bits.length + 3) = PMF.pure (seekBitstringNextFinish before bits rest output) :=
  (seekBitstringNext_runs before bits rest output).evalConfigWithin_eq_pure_of_no_randomBit
    GuardedCompiler.seekScratchInput_no_randomBit

theorem seekBitstringNextStart_layout (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) :
    seekBitstringNextStart before bits rest output =
      { inputTape := { ({ right := bits.map some ++ none :: rest } : Tape).moveRight with left := before },
        outputTape := output } := by
  cases bits <;> simp [seekBitstringNextStart, tapeAtCells, Tape.moveRight]

theorem seekBitstringNextFinish_layout (before : List (Option Bool)) (bits : List Bool)
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    seekBitstringNextFinish before bits (current :: right) output =
      { pc := 4,
        inputTape := { left := none :: (bits.reverse.map some ++ before), current := current, right := right },
        outputTape := output, halted := true } := rfl

/-- Explicit layout even when the caller has no represented cells beyond
its separator. A missing outer cell still denotes a blank, without erasing
any stored cell in the native execution. -/
theorem seekBitstringNextFinish_layout_cells (before : List (Option Bool)) (bits : List Bool)
    (rest : List (Option Bool)) (output : Tape) :
    seekBitstringNextFinish before bits rest output =
      { pc := 4,
        inputTape := { ({ right := rest } : Tape).moveRight with
          left := none :: bits.reverse.map some ++ before },
        outputTape := output, halted := true } := by
  cases rest <;> rfl

end Machine
