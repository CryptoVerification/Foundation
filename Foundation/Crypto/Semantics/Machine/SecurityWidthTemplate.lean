import Foundation.Crypto.Semantics.Machine.FramedColumnSlotFill

namespace Machine.SecurityWidthTemplate

/-- Consume the unary security parameter and write three blank-valued bit
cells per unit, followed by nine more cells for the fixed `+ 3` width of
the prime-order representation. The input head stops at the instance frame;
no parameter or group operation is an instruction. -/
def program : Program :=
  [.branch .input 28 9 1,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .moveRight .input, .jump 0,
   .moveRight .input,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .halt]

private def state (before : List (Option Bool)) (remaining : List Bool)
    (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := before },
    outputTape := output }

private def finish (before : List (Option Bool)) (remaining : List Bool)
    (output : Tape) : Configuration :=
  { pc := 28, inputTape := { Tape.ofBits remaining with left := before },
    outputTape := output, halted := true }

private def writeThree (output : Tape) : Tape :=
  (((((output.write (some false)).moveRight).write (some false)).moveRight).write
    (some false)).moveRight

private def writeNine (output : Tape) : Tape :=
  writeThree (writeThree (writeThree output))

private theorem eval_true (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    evalConfigWithin program (state before (true :: rest) output) 9 =
      PMF.pure (state (some true :: before) rest (writeThree output)) := by
  cases rest <;> cases output with
  | mk left current right =>
      simp [evalConfigWithin, stepPMF, next, program, state, writeThree,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write,
        PMF.pure_bind]

private theorem eval_end (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    evalConfigWithin program (state before (false :: rest) output) 21 =
      PMF.pure (finish (some false :: before) rest (writeNine output)) := by
  cases rest <;> cases output with
  | mk left current right =>
      simp [evalConfigWithin, stepPMF, next, program, state, finish,
        writeNine, writeThree, Instruction.next, Configuration.advance,
        Configuration.tape, Configuration.updateTape, Tape.ofBits,
        Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem writeThree_blank (before : List (Option Bool)) :
    writeThree ({ left := before } : Tape) =
      { left := List.replicate 3 (some false) ++ before } := by
  simp [writeThree, Tape.write, Tape.moveRight]

private theorem writeNine_blank (before : List (Option Bool)) :
    writeNine ({ left := before } : Tape) =
      { left := List.replicate 9 (some false) ++ before } := by
  simp [writeNine, writeThree_blank]

theorem blankColumns (width : Nat) :
    List.replicate (3 * width) false =
      BinaryThirdColumnTemplate.columns (List.replicate width false) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp [BinaryThirdColumnTemplate.columns,
        BinaryModularAddition.interleave, List.replicate_succ,
        Nat.mul_succ, ih]

/-- On a valid unary prefix, the exact physical output contains
`3 * (n + 3)` written cells, and the original instance frame is unread. -/
theorem eval_context (n : Nat) (rest : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state beforeInput (encodeSecurityParameter n ++ rest)
        { left := beforeOutput })
      (9 * n + 21) =
    PMF.pure (finish
      (some false :: List.replicate n (some true) ++ beforeInput) rest
      { left := List.replicate (3 * (n + 3)) (some false) ++ beforeOutput }) := by
  induction n generalizing beforeInput beforeOutput with
  | zero =>
      simpa [encodeSecurityParameter, writeNine_blank] using
        eval_end beforeInput rest ({ left := beforeOutput } : Tape)
  | succ n ih =>
      have hTime : 9 * (n + 1) + 21 = 9 + (9 * n + 21) := by omega
      have hPrefix : encodeSecurityParameter (n + 1) ++ rest =
          true :: (encodeSecurityParameter n ++ rest) := by
        simp [encodeSecurityParameter, List.replicate_succ, List.append_assoc]
      rw [hPrefix]
      rw [hTime, evalConfigWithin_add]
      rw [eval_true]
      simp only [PMF.pure_bind]
      rw [writeThree_blank]
      have hIH := ih (some true :: beforeInput)
        (List.replicate 3 (some false) ++ beforeOutput)
      simpa [List.replicate_add, List.append_assoc,
        Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hIH

theorem eval_valid (n : Nat) (rest : List Bool) :
    evalConfigWithin program
      (Configuration.initial (encodeSecurityParameter n ++ rest))
      (9 * n + 21) =
    PMF.pure (finish
      (some false :: List.replicate n (some true)) rest
      { left := List.replicate (3 * (n + 3)) (some false) }) := by
  have hInitial : Configuration.initial (encodeSecurityParameter n ++ rest) =
      state [] (encodeSecurityParameter n ++ rest) { left := [] } := by
    cases n <;> rfl
  rw [hInitial, eval_context]
  simp

theorem eval_output (n : Nat) (rest : List Bool) :
    evalWithin program (encodeSecurityParameter n ++ rest) (9 * n + 21) =
      PMF.pure (some (List.replicate (3 * (n + 3)) false)) := by
  unfold evalWithin
  rw [eval_valid, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits]

theorem runs_valid (n : Nat) (rest : List Bool) :
    ∃ target used, used ≤ 9 * n + 21 ∧
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++ rest)) target used ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := some false :: List.replicate n (some true) } ∧
      target.outputTape =
        { left := List.replicate (3 * (n + 3)) (some false) } := by
  let target := finish (some false :: List.replicate n (some true)) rest
    { left := List.replicate (3 * (n + 3)) (some false) }
  have hMem : target ∈
      (evalConfigWithin program
        (Configuration.initial (encodeSecurityParameter n ++ rest))
        (9 * n + 21)).support := by
    rw [eval_valid]
    simp [target]
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem).toRunsFor_le
  exact ⟨target, used, hUsed, run, rfl, rfl, rfl⟩

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_extend {start finish : Configuration} {steps : Nat}
    (h : evalConfigWithin program start steps = PMF.pure finish)
    (hHalted : finish.halted = true) (extra : Nat) :
    evalConfigWithin program start (steps + extra) = PMF.pure finish := by
  rw [evalConfigWithin_add, h, PMF.pure_bind, eval_halted finish extra hHalted]

private theorem eval_blank (before : List (Option Bool)) (output : Tape) :
    evalConfigWithin program (state before [] output) 2 =
      PMF.pure (finish before [] output) := by
  simp [evalConfigWithin, stepPMF, next, program, state, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

/-- An unterminated unary header still halts at the first blank, leaving
exactly three output cells for each consumed `true` bit. -/
theorem eval_unterminated (n : Nat)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state beforeInput (List.replicate n true) { left := beforeOutput })
      (9 * n + 2) =
    PMF.pure (finish
      (List.replicate n (some true) ++ beforeInput) []
      { left := List.replicate (3 * n) (some false) ++ beforeOutput }) := by
  induction n generalizing beforeInput beforeOutput with
  | zero =>
      simpa using eval_blank beforeInput ({ left := beforeOutput } : Tape)
  | succ n ih =>
      have hTime : 9 * (n + 1) + 2 = 9 + (9 * n + 2) := by omega
      rw [hTime, List.replicate_succ, evalConfigWithin_add,
        eval_true, PMF.pure_bind, writeThree_blank]
      simpa [Nat.mul_succ, List.replicate_add, List.append_assoc] using
        ih (some true :: beforeInput)
          (List.replicate 3 (some false) ++ beforeOutput)

private theorem split_header (bits : List Bool) :
    (∃ n, bits = List.replicate n true) ∨
      (∃ n rest, bits = encodeSecurityParameter n ++ rest) := by
  induction bits with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit rest ih =>
      cases bit with
      | false => exact Or.inr ⟨0, rest, rfl⟩
      | true =>
          rcases ih with ⟨n, h⟩ | ⟨n, tail, h⟩
          · exact Or.inl ⟨n + 1, by simp [h, List.replicate_succ]⟩
          · exact Or.inr ⟨n + 1, tail, by
              simp [h, encodeSecurityParameter, List.replicate_succ,
                List.append_assoc]⟩

/-- Every finite initial input yields a concrete halted trace and an output
block with a multiple-of-three length, even without a unary delimiter. -/
theorem runs_any_layout_prefix (bits : List Bool) :
    ∃ target used width rest before,
      used ≤ 9 * bits.length + 21 ∧
      width ≤ bits.length + 3 ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits rest with left := before } ∧
      target.outputTape =
        { left := List.replicate (3 * width) (some false) } ∧
      rest.length ≤ bits.length ∧
      (rest ≠ [] → ∃ n,
        bits = encodeSecurityParameter n ++ rest ∧
        width = n + 3 ∧
        before = some false :: List.replicate n (some true)) := by
  rcases split_header bits with ⟨n, hBits⟩ | ⟨n, rest, hBits⟩
  · subst bits
    let target := finish (List.replicate n (some true)) []
      { left := List.replicate (3 * n) (some false) }
    have hEval : evalConfigWithin program
        (Configuration.initial (List.replicate n true)) (9 * n + 2) =
        PMF.pure target := by
      have hInitial : Configuration.initial (List.replicate n true) =
          state [] (List.replicate n true) { left := [] } := by
        cases n <;> rfl
      rw [hInitial]
      simpa [target] using eval_unterminated n [] []
    obtain ⟨used, hUsed, run⟩ :=
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp
        (by rw [hEval]; simp : target ∈
          (evalConfigWithin program
            (Configuration.initial (List.replicate n true)) (9 * n + 2)).support)).toRunsFor_le
    refine ⟨target, used, n, [], List.replicate n (some true), ?_, ?_,
      run, rfl, rfl, rfl, by simp, ?_⟩
    · simp at *
      omega
    · simp
    · intro hRest
      exact False.elim (hRest rfl)
  · subst bits
    obtain ⟨target, used, hUsed, run, hHalt, hInput, hOutput⟩ :=
      runs_valid n rest
    refine ⟨target, used, n + 3, rest,
      some false :: List.replicate n (some true), ?_, ?_, run, hHalt,
      hInput, hOutput, ?_, ?_⟩
    · simp [encodeSecurityParameter] at *
      omega
    · simp [encodeSecurityParameter]
    · simp [encodeSecurityParameter]
      omega
    · intro _
      exact ⟨n, rfl, rfl, rfl⟩

theorem runs_any_layout (bits : List Bool) :
    ∃ target used width rest before,
      used ≤ 9 * bits.length + 21 ∧
      width ≤ bits.length + 3 ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits rest with left := before } ∧
      target.outputTape =
        { left := List.replicate (3 * width) (some false) } ∧
      rest.length ≤ bits.length := by
  obtain ⟨target, used, width, rest, before, hUsed, hWidth, run,
    hHalt, hInput, hOutput, hRest, _⟩ := runs_any_layout_prefix bits
  exact ⟨target, used, width, rest, before, hUsed, hWidth,
    run, hHalt, hInput, hOutput, hRest⟩

/-- Every finite input, including a missing unary delimiter, terminates.
The output tape may already contain arbitrary cells. -/
theorem all_context (before : List (Option Bool))
    (bits : List Bool) (output : Tape) :
    ∃ target,
      evalConfigWithin program (state before bits output)
        (9 * bits.length + 21) = PMF.pure target ∧ target.halted = true := by
  induction bits generalizing before output with
  | nil =>
      refine ⟨finish before [] output, ?_, rfl⟩
      change evalConfigWithin program (state before [] output) 21 = _
      simpa only [show (21 : Nat) = 2 + 19 by omega] using
        eval_extend (eval_blank before output) rfl 19
  | cons bit rest ih =>
      cases bit with
      | false =>
          refine ⟨finish (some false :: before) rest (writeNine output), ?_, rfl⟩
          have hTime : 9 * (false :: rest).length + 21 =
              21 + (9 * rest.length + 9) := by simp; omega
          rw [hTime]
          exact eval_extend (eval_end before rest output) rfl (9 * rest.length + 9)
      | true =>
          obtain ⟨target, hEval, hHalted⟩ := ih (some true :: before)
            (writeThree output)
          refine ⟨target, ?_, hHalted⟩
          have hTime : 9 * (true :: rest).length + 21 =
              9 + (9 * rest.length + 21) := by simp; omega
          rw [hTime, evalConfigWithin_add, eval_true, PMF.pure_bind]
          exact hEval

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (9 * bits.length + 21) := by
  obtain ⟨target, hEval, hHalted⟩ := all_context [] bits ({} : Tape)
  apply haltsWithin_of_no_timeout_support program bits _
  have hInitial : Configuration.initial bits = state [] bits ({} : Tape) := by
    cases bits <;> rfl
  unfold evalWithin
  rw [hInitial, hEval, PMF.pure_map]
  simp [hHalted]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨fun length => 9 * length + 21, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 9).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 21)

end Machine.SecurityWidthTemplate
