import Foundation.Machine.SecurityWidthTemplate

namespace Machine.TwoFieldColumnSkip

/-- Use each populated three-cell output column as a counter while moving
the input head across two consecutive fixed-width instance fields. The
output bits are only read; malformed input bits have no effect on control. -/
def program : Program :=
  [.branch .output 7 1 1,
   .moveRight .input, .moveRight .input,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .jump 0, .halt]

private def state (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def finish (input output : Tape) : Configuration :=
  { pc := 7, inputTape := input, outputTape := output, halted := true }

private theorem eval_step (input output : Tape)
    (hCurrent : output.current ≠ none) :
    evalConfigWithin program (state input output) 7 =
      PMF.pure (state input.moveRight.moveRight
        output.moveRight.moveRight.moveRight) := by
  cases output with
  | mk left current right =>
    cases current with
    | none => contradiction
    | some bit =>
        cases bit <;>
          simp [evalConfigWithin, stepPMF, next, program, state,
            Instruction.next, Configuration.advance, Configuration.tape,
            Configuration.updateTape, Tape.moveRight, PMF.pure_bind]

private theorem eval_end (input output : Tape)
    (hCurrent : output.current = none) :
    evalConfigWithin program (state input output) 2 =
      PMF.pure (finish input output) := by
  cases output with
  | mk left current right =>
    cases current with
    | none =>
        simp [evalConfigWithin, stepPMF, next, program, state, finish,
          Instruction.next, Configuration.tape, PMF.pure_bind]
    | some bit => contradiction

/-- On a three-cell output matrix, one native loop iteration advances over
two actual input cells while preserving every output bit. -/
theorem eval_columns (columns : List BinaryModularAddition.Column)
    (skipped tail : List Bool)
    (hLength : skipped.length = 2 * columns.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state
        { Tape.ofBits (skipped ++ tail) with left := beforeInput }
        { Tape.ofBits (BinaryModularAddition.interleave columns) with
          left := beforeOutput })
      (7 * columns.length + 2) =
    PMF.pure (finish
      { Tape.ofBits tail with left := skipped.reverse.map some ++ beforeInput }
      { left := (BinaryModularAddition.interleave columns).reverse.map some ++
          beforeOutput }) := by
  induction columns generalizing skipped beforeInput beforeOutput with
  | nil =>
      have hEmpty : skipped = [] := List.length_eq_zero_iff.mp (by simpa using hLength)
      subst skipped
      simpa [BinaryModularAddition.interleave, Tape.ofBits] using
        eval_end ({ Tape.ofBits tail with left := beforeInput })
          ({ left := beforeOutput } : Tape) rfl
  | cons column rest ih =>
      obtain ⟨a, b, suffix, hSkipped⟩ :
          ∃ a b suffix, skipped = a :: b :: suffix := by
        cases skipped with
        | nil => simp at hLength
        | cons a tail =>
            cases tail with
            | nil => simp at hLength; omega
            | cons b suffix => exact ⟨a, b, suffix, rfl⟩
      subst skipped
      have hRest : suffix.length = 2 * rest.length := by
        simp at hLength
        omega
      rcases column with ⟨⟨first, second⟩, modulus⟩
      have hCurrent :
          ({ Tape.ofBits (BinaryModularAddition.interleave
              (((first, second), modulus) :: rest)) with
              left := beforeOutput } : Tape).current ≠ none := by
        simp [BinaryModularAddition.interleave, Tape.ofBits]
      have hInputStep :
          (({ Tape.ofBits ((a :: b :: suffix) ++ tail) with
            left := beforeInput } : Tape).moveRight).moveRight =
            { Tape.ofBits (suffix ++ tail) with
              left := [some b, some a] ++ beforeInput } := by
        cases suffix <;> cases tail <;>
          simp [Tape.ofBits, Tape.moveRight]
      have hOutputStep :
          ((({ Tape.ofBits (BinaryModularAddition.interleave
              (((first, second), modulus) :: rest)) with
              left := beforeOutput } : Tape).moveRight).moveRight).moveRight =
            { Tape.ofBits (BinaryModularAddition.interleave rest) with
              left := [some modulus, some second, some first] ++ beforeOutput } := by
        cases rest <;>
          simp [BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight]
      have hTime : 7 * (((first, second), modulus) :: rest).length + 2 =
          7 + (7 * rest.length + 2) := by simp; omega
      rw [hTime, evalConfigWithin_add]
      simp only [eval_step _ _ hCurrent, PMF.pure_bind,
        hInputStep, hOutputStep]
      convert ih suffix hRest
        ([some b, some a] ++ beforeInput)
        ([some modulus, some second, some first] ++ beforeOutput) using 1;
        simp [BinaryModularAddition.interleave,
          List.reverse_cons,
          List.map_append, List.append_assoc]

/-- When the second and third instance fields have the modulus width, this
finite scan stops at the following element frame. The exact remaining
modulus columns stay on the output tape. -/
theorem eval_instance_fields (modulus second third following : List Bool)
    (hSecond : second.length = modulus.length)
    (hThird : third.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      { inputTape := { Tape.ofBits (second ++ third ++ following) with
          left := beforeInput },
        outputTape := { Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
          left := beforeOutput } }
      (7 * modulus.length + 2) =
    PMF.pure
      { pc := 7,
        inputTape := { Tape.ofBits following with
          left := (second ++ third).reverse.map some ++ beforeInput },
        outputTape :=
          { left := (BinaryThirdColumnTemplate.columns modulus).reverse.map some ++
              beforeOutput },
        halted := true } := by
  have hLength : (second ++ third).length =
      2 * (modulus.map fun bit => ((false, false), bit)).length := by
    simp [hSecond, hThird]
    omega
  simpa [state, finish, BinaryThirdColumnTemplate.columns,
    List.append_assoc] using
    eval_columns (modulus.map fun bit => ((false, false), bit))
      (second ++ third) following hLength beforeInput beforeOutput

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

private theorem right_length_lt (output : Tape)
    (hCurrent : output.current ≠ none) (hRight : output.right ≠ []) :
    (output.moveRight.moveRight.moveRight).right.length < output.right.length := by
  cases output with
  | mk left current right =>
    cases right with
    | nil => contradiction
    | cons a tail =>
        cases tail with
        | nil => simp [Tape.moveRight]
        | cons b tail =>
            cases tail with
            | nil => simp [Tape.moveRight]
            | cons c tail => simp [Tape.moveRight]; omega

/-- The output tape is the finite loop counter. Every three-cell head
advance strictly shortens its unread suffix; even arbitrary malformed
physical tapes therefore terminate. -/
theorem all_context (input output : Tape) :
    ∃ target,
      evalConfigWithin program (state input output)
        (7 * (output.right.length + 1) + 2) = PMF.pure target ∧
      target.halted = true := by
  suffices hAux : ∀ n (input output : Tape), output.right.length = n →
      ∃ target,
        evalConfigWithin program (state input output) (7 * (n + 1) + 2) =
          PMF.pure target ∧ target.halted = true from
    hAux output.right.length input output rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro input output hLength
      by_cases hCurrent : output.current = none
      · refine ⟨finish input output, ?_, rfl⟩
        have h := eval_end input output hCurrent
        simpa only [show 7 * (n + 1) + 2 = 2 + 7 * (n + 1) by omega] using
          eval_extend h rfl (7 * (n + 1))
      · let nextInput := input.moveRight.moveRight
        let nextOutput := output.moveRight.moveRight.moveRight
        by_cases hRight : output.right = []
        · have hZero : n = 0 := by simpa [hRight] using hLength.symm
          have hNext : nextOutput.current = none := by
            cases output with
            | mk left current right =>
                cases right with
                | nil => simp [nextOutput, Tape.moveRight]
                | cons a rest => contradiction
          refine ⟨finish nextInput nextOutput, ?_, rfl⟩
          have hTime : 7 * (n + 1) + 2 = 7 + 2 := by omega
          rw [hTime, evalConfigWithin_add,
            eval_step input output hCurrent, PMF.pure_bind]
          exact eval_end nextInput nextOutput hNext
        · have hLess : nextOutput.right.length < n := by
            simpa only [nextOutput, ← hLength] using
              right_length_lt output hCurrent hRight
          obtain ⟨target, hEval, hHalted⟩ :=
            ih nextOutput.right.length hLess nextInput nextOutput rfl
          refine ⟨target, ?_, hHalted⟩
          have hLe : 7 + (7 * (nextOutput.right.length + 1) + 2) ≤
              7 * (n + 1) + 2 := by omega
          have hTime : 7 * (n + 1) + 2 =
              (7 + (7 * (nextOutput.right.length + 1) + 2)) +
                ((7 * (n + 1) + 2) -
                  (7 + (7 * (nextOutput.right.length + 1) + 2))) := by omega
          rw [hTime]
          apply eval_extend _ hHalted _
          rw [evalConfigWithin_add,
            eval_step input output hCurrent, PMF.pure_bind]
          exact hEval

private theorem moveRight_twice_suffix (bits : List Bool)
    (before : List (Option Bool)) :
    ∃ remaining before',
      ({ Tape.ofBits bits with left := before } : Tape).moveRight.moveRight =
        { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  cases bits with
  | nil => exact ⟨[], none :: none :: before, rfl, by simp⟩
  | cons first rest =>
      cases rest with
      | nil => exact ⟨[], none :: some first :: before, rfl, by simp⟩
      | cons second tail =>
          refine ⟨tail, some second :: some first :: before, ?_, by simp; omega⟩
          cases tail <;> rfl

/-- The arbitrary-output field skip preserves the contiguous unread suffix
of an initially contiguous input, including when it advances past the end. -/
theorem all_context_suffix (bits : List Bool)
    (before : List (Option Bool)) (output : Tape) :
    ∃ target remaining before',
      evalConfigWithin program
        (state { Tape.ofBits bits with left := before } output)
        (7 * (output.right.length + 1) + 2) = PMF.pure target ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  suffices hAux : ∀ k (bits : List Bool) (before : List (Option Bool))
      (output : Tape), output.right.length = k →
      ∃ target remaining before',
        evalConfigWithin program
          (state { Tape.ofBits bits with left := before } output)
          (7 * (k + 1) + 2) = PMF.pure target ∧
        target.halted = true ∧
        target.inputTape = { Tape.ofBits remaining with left := before' } ∧
        remaining.length ≤ bits.length from
    hAux output.right.length bits before output rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro bits before output hLength
      let input : Tape := { Tape.ofBits bits with left := before }
      by_cases hCurrent : output.current = none
      · refine ⟨finish input output, bits, before, ?_, rfl, rfl, le_refl _⟩
        have h := eval_end input output hCurrent
        simpa only [show 7 * (k + 1) + 2 = 2 + 7 * (k + 1) by omega] using
          eval_extend h rfl (7 * (k + 1))
      · obtain ⟨remaining, before', hInput, hRemaining⟩ :=
          moveRight_twice_suffix bits before
        let nextInput := input.moveRight.moveRight
        let nextOutput := output.moveRight.moveRight.moveRight
        by_cases hRight : output.right = []
        · have hZero : k = 0 := by simpa [hRight] using hLength.symm
          have hNext : nextOutput.current = none := by
            cases output with
            | mk left current right =>
                cases right with
                | nil => simp [nextOutput, Tape.moveRight]
                | cons a rest => contradiction
          refine ⟨finish nextInput nextOutput, remaining, before', ?_,
            rfl, hInput, hRemaining⟩
          have hTime : 7 * (k + 1) + 2 = 7 + 2 := by omega
          rw [hTime, evalConfigWithin_add,
            eval_step input output hCurrent, PMF.pure_bind]
          exact eval_end nextInput nextOutput hNext
        · have hLess : nextOutput.right.length < k := by
            simpa only [nextOutput, ← hLength] using
              right_length_lt output hCurrent hRight
          obtain ⟨target, finalBits, finalBefore, hEval, hHalted,
            hFinalInput, hFinalLength⟩ :=
            ih nextOutput.right.length hLess remaining before' nextOutput rfl
          refine ⟨target, finalBits, finalBefore, ?_, hHalted,
            hFinalInput, ?_⟩
          · have hLe : 7 + (7 * (nextOutput.right.length + 1) + 2) ≤
                7 * (k + 1) + 2 := by omega
            have hTime : 7 * (k + 1) + 2 =
                (7 + (7 * (nextOutput.right.length + 1) + 2)) +
                  ((7 * (k + 1) + 2) -
                    (7 + (7 * (nextOutput.right.length + 1) + 2))) := by omega
            rw [hTime]
            apply eval_extend _ hHalted _
            rw [evalConfigWithin_add,
              eval_step input output hCurrent, PMF.pure_bind]
            rw [← hInput] at hEval
            simpa [nextInput, nextOutput] using hEval
          · omega

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits 9 := by
  obtain ⟨target, hEval, hHalted⟩ := all_context (Tape.ofBits bits) ({} : Tape)
  apply haltsWithin_of_no_timeout_support program bits _
  unfold evalWithin
  have hInitial : Configuration.initial bits = state (Tape.ofBits bits) ({} : Tape) := rfl
  rw [hInitial]
  have hEval' : evalConfigWithin program (state (Tape.ofBits bits) ({} : Tape)) 9 =
      PMF.pure target := by simpa using hEval
  rw [hEval', PMF.pure_map]
  simp [hHalted]

theorem polynomialTime : PolynomialTime program := by
  exact ⟨fun _ => 9, PolynomiallyBounded.const 9, haltsWithin⟩

end Machine.TwoFieldColumnSkip
