import Foundation.Machine.Adversary
import Foundation.Machine.PolynomialTime
import Foundation.Machine.SubroutineSimulation

namespace Machine

/-- Consume a unary security-parameter field, retaining its cells. A false
terminator is consumed; a missing terminator halts on blank. The other tape
is untouched. Each scan iteration performs three native transitions. -/
def skipUnary : Program :=
  [.branch .input 5 1 3, .moveRight .input, .halt,
   .moveRight .input, .jump 0, .halt]

def skipUnaryStart (before : List (Option Bool)) (n : Nat) (rest : List Bool)
    (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits (encodeSecurityParameter n ++ rest) with left := before },
    outputTape := output }

def skipUnaryFinish (before : List (Option Bool)) (n : Nat) (rest : List Bool)
    (output : Tape) : Configuration :=
  { pc := 2,
    inputTape := { Tape.ofBits rest with
      left := some false :: (List.replicate n (some true) ++ before) },
    outputTape := output,
    halted := true }

theorem skipUnary_runs (before : List (Option Bool)) (n : Nat) (rest : List Bool)
    (output : Tape) :
    RunsFor skipUnary (skipUnaryStart before n rest output)
      (skipUnaryFinish before n rest output) (3 * n + 3) := by
  induction n generalizing before with
  | zero =>
      let start := skipUnaryStart before 0 rest output
      let selected : Configuration := { start with pc := 1 }
      let moved : Configuration := { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, skipUnaryStart,
          encodeSecurityParameter, Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected moved := by
        simp [Step, successors, next, skipUnary, start, selected, moved, skipUnaryStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipUnary moved (skipUnaryFinish before 0 rest output) := by
        cases rest <;> simp [Step, successors, next, skipUnary, start, selected, moved,
          skipUnaryStart, skipUnaryFinish, encodeSecurityParameter, Tape.ofBits,
          Tape.moveRight, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | succ n ih =>
      let start := skipUnaryStart before (n + 1) rest output
      let selected : Configuration := { start with pc := 3 }
      let moved : Configuration := { selected with pc := 4, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, skipUnaryStart,
          encodeSecurityParameter, List.replicate_succ, Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected moved := by
        simp [Step, successors, next, skipUnary, start, selected, moved, skipUnaryStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipUnary moved (skipUnaryStart (some true :: before) n rest output) := by
        cases n <;>
          simp [Step, successors, next, skipUnary, start, selected, moved,
            skipUnaryStart, encodeSecurityParameter, List.replicate_succ, Tape.ofBits,
            Tape.moveRight, Instruction.next]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2).trans
        (ih (some true :: before))
      have hFinish : skipUnaryFinish (some true :: before) n rest output =
          skipUnaryFinish before (n + 1) rest output := by
        simp [skipUnaryFinish, List.replicate_succ', List.append_assoc]
      rw [hFinish] at run
      convert run using 1
      omega

theorem skipUnary_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ skipUnary := by
  simp [skipUnary]

theorem skipUnary_eval (before : List (Option Bool)) (n : Nat) (rest : List Bool)
    (output : Tape) :
    evalConfigWithin skipUnary (skipUnaryStart before n rest output) (3 * n + 3) =
      PMF.pure (skipUnaryFinish before n rest output) :=
  (skipUnary_runs before n rest output).evalConfigWithin_eq_pure_of_no_randomBit skipUnary_no_randomBit

theorem skipUnary_control_closed (c d : Configuration)
    (hPc : c.pc < skipUnary.length) (step : Step skipUnary c d)
    (_hRunning : d.halted = false) : d.pc < skipUnary.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 6 at hPc
  change d.pc < 6
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, skipUnary,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem skipUnary_unterminated (before : List (Option Bool)) (n : Nat) (output : Tape) :
    RunsFor skipUnary
      ({
        inputTape := { Tape.ofBits (List.replicate n true) with left := before }
        outputTape := output } : Configuration)
      ({
        pc := 5
        inputTape := { left := List.replicate n (some true) ++ before }
        outputTape := output, halted := true } : Configuration) (3 * n + 2) := by
  induction n generalizing before with
  | zero =>
      let start : Configuration := { inputTape := { left := before }, outputTape := output }
      let selected : Configuration := { start with pc := 5 }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected { selected with halted := true } := by
        simp [Step, successors, next, skipUnary, start, selected, Instruction.next]
      simpa [start, selected, Tape.ofBits] using RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | succ n ih =>
      let start : Configuration :=
        {
          inputTape := { Tape.ofBits (List.replicate (n + 1) true) with left := before }
          outputTape := output }
      let selected : Configuration := { start with pc := 3 }
      let moved : Configuration := { selected with pc := 4, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipUnary start selected := by
        simp [Step, successors, next, skipUnary, start, selected, List.replicate_succ,
          Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step skipUnary selected moved := by
        simp [Step, successors, next, skipUnary, start, selected, moved,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipUnary moved
          ({
            inputTape := { Tape.ofBits (List.replicate n true) with left := some true :: before }
            outputTape := output } : Configuration) := by
        cases n <;> simp [Step, successors, next, skipUnary, start, selected, moved,
          List.replicate_succ, Tape.ofBits, Tape.moveRight, Instruction.next]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2).trans
        (ih (some true :: before))
      convert run using 1
      · simp [List.replicate_succ', List.append_assoc]
      · omega

private theorem unary_split (input : List Bool) :
    (∃ n, input = List.replicate n true) ∨
      (∃ n rest, input = List.replicate n true ++ false :: rest) := by
  induction input with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit rest ih =>
      cases bit with
      | false => exact Or.inr ⟨0, rest, rfl⟩
      | true =>
          rcases ih with ⟨n, h⟩ | ⟨n, tail, h⟩
          · exact Or.inl ⟨n + 1, by simp [h, List.replicate_succ]⟩
          · exact Or.inr ⟨n + 1, tail, by simp [h, List.replicate_succ]⟩

/-- All finite raw inputs, including a missing unary terminator, stop
within a linear bound. The assertion quantifies actual native traces. -/
theorem skipUnary_terminates_from (before : List (Option Bool)) (input : List Bool)
    (output : Tape) :
    ∃ finish used, used ≤ 3 * input.length + 3 ∧
      RunsFor skipUnary
        ({ inputTape := { Tape.ofBits input with left := before }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  rcases unary_split input with ⟨n, hInput⟩ | ⟨n, rest, hInput⟩
  · subst input
    refine ⟨_, 3 * n + 2, ?_, skipUnary_unterminated before n output, rfl⟩
    simp only [List.length_replicate]
    omega
  · subst input
    refine ⟨skipUnaryFinish before n rest output, 3 * n + 3, ?_, ?_, rfl⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · simpa [skipUnaryStart, encodeSecurityParameter, List.append_assoc] using
        skipUnary_runs before n rest output

/-- The native scan leaves a contiguous suffix of the original finite input,
even when its terminator is missing. This layout fact lets the next parser
consume the retained tape without reloading or replacing any caller data. -/
theorem skipUnary_terminates_with_suffix (before : List (Option Bool)) (input : List Bool)
    (output : Tape) :
    ∃ (finish : Configuration) (used : Nat) (left : List (Option Bool)) (rest : List Bool),
      used ≤ 3 * input.length + 3 ∧ rest.length ≤ input.length ∧
      RunsFor skipUnary
        ({ inputTape := { Tape.ofBits input with left := before }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { Tape.ofBits rest with left := left } ∧ finish.outputTape = output := by
  rcases unary_split input with ⟨n, hInput⟩ | ⟨n, rest, hInput⟩
  · subst input
    refine ⟨_, 3 * n + 2, List.replicate n (some true) ++ before, [], ?_, ?_,
      skipUnary_unterminated before n output, rfl, rfl, rfl⟩
    · simp only [List.length_replicate]; omega
    · simp
  · subst input
    refine ⟨skipUnaryFinish before n rest output, 3 * n + 3,
      some false :: (List.replicate n (some true) ++ before), rest, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
    · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
    · simpa [skipUnaryStart, encodeSecurityParameter, List.append_assoc] using
        skipUnary_runs before n rest output

theorem skipUnary_haltsWithin (input : List Bool) :
    HaltsWithin skipUnary input (3 * input.length + 3) := by
  obtain ⟨finish, used, hBound, run, hHalted⟩ := skipUnary_terminates_from [] input {}
  have hInitial : ({ inputTape := { Tape.ofBits input with left := [] } } : Configuration) =
      Configuration.initial input := by cases input <;> rfl
  rw [hInitial] at run
  have hHalts : HaltsWith skipUnary input finish.outputBits used := ⟨finish, run, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit skipUnary_no_randomBit).mono hBound

theorem skipUnary_polynomialTime : PolynomialTime skipUnary := by
  refine ⟨fun m => 3 * m + 3, ?_, skipUnary_haltsWithin⟩
  exact ((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3)

private theorem skipUnary_blank_from_anyTape (input output : Tape)
    (hBlank : input.current = none) :
    RunsFor skipUnary ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 5, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have h0 : Step skipUnary ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 5, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, skipUnary, Instruction.next, Configuration.tape, hBlank]
  have h1 : Step skipUnary ({ pc := 5, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 5, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, skipUnary, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem skipUnary_bit_from_anyTape (input output : Tape) (bit : Bool)
    (hBit : input.current = some bit) :
    RunsFor skipUnary ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := if bit then 0 else 2, inputTape := input.moveRight,
         outputTape := output, halted := !bit } : Configuration) 3 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := if bit then 3 else 1 }
  let moved : Configuration := { selected with pc := if bit then 4 else 2, inputTape := input.moveRight }
  have h0 : Step skipUnary start selected := by
    cases bit <;> simp [Step, successors, next, skipUnary, start, selected,
      Instruction.next, Configuration.tape, hBit]
  have h1 : Step skipUnary selected moved := by
    cases bit <;> simp [Step, successors, next, skipUnary, start, selected, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step skipUnary moved
      ({ pc := if bit then 0 else 2, inputTape := input.moveRight,
         outputTape := output, halted := !bit } : Configuration) := by
    cases bit <;> simp [Step, successors, next, skipUnary, start, selected, moved, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2

private theorem skipUnary_finite_cells (left right : List (Option Bool))
    (current : Option Bool) (output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 3 * (right.length + 1) + 3 ∧
      RunsFor skipUnary
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.outputTape = output := by
  induction right generalizing left current with
  | nil =>
      cases current with
      | none => exact ⟨_, 2, by simp, skipUnary_blank_from_anyTape _ output rfl, rfl, rfl⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit }
          have hBit := skipUnary_bit_from_anyTape input output bit rfl
          cases bit with
          | false => exact ⟨_, 3, by simp, hBit, rfl, rfl⟩
          | true =>
              have hBlank := skipUnary_blank_from_anyTape input.moveRight output rfl
              exact ⟨_, 5, by simp, hBit.trans hBlank, rfl, rfl⟩
  | cons cell rest ih =>
      cases current with
      | none => exact ⟨_, 2, by simp, skipUnary_blank_from_anyTape _ output rfl, rfl, rfl⟩
      | some bit =>
          let input : Tape := { left := left, current := some bit, right := cell :: rest }
          have hBit := skipUnary_bit_from_anyTape input output bit rfl
          cases bit with
          | false => exact ⟨_, 3, by simp, hBit, rfl, rfl⟩
          | true =>
              obtain ⟨finish, used, hBound, hRun, hHalted, hOutput⟩ := ih (some true :: left) cell
              change RunsFor skipUnary
                ({ inputTape := input.moveRight, outputTape := output } : Configuration) finish used at hRun
              refine ⟨finish, 3 + used, ?_, hBit.trans hRun, hHalted, hOutput⟩
              simp only [List.length_cons]
              omega

/-- Runtime safety for an invocation after arbitrary retained-tape work.
The scan stops at the first false bit or blank, including an internal blank;
the opposite tape is preserved. No well-formed unary field is required. -/
theorem skipUnary_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 3 * input.cells + 3 ∧
      RunsFor skipUnary ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, hBound, hRun, hHalted, hOutput⟩ :=
    skipUnary_finite_cells input.left input.right input.current output
  refine ⟨finish, used, ?_, hRun, hHalted, hOutput⟩
  dsimp only [Tape.cells]
  omega

end Machine
