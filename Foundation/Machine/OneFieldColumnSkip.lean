import Foundation.Machine.SecurityWidthTemplate

namespace Machine.OneFieldColumnSkip

/-- Use each populated three-cell output column as a counter while moving
the input head across one fixed-width instance field. The
output bits are only read; malformed input bits have no effect on control. -/
def program : Program :=
  [.branch .output 6 1 1,
   .moveRight .input,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .jump 0, .halt]

private def state (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def finish (input output : Tape) : Configuration :=
  { pc := 6, inputTape := input, outputTape := output, halted := true }

private theorem eval_step (input output : Tape)
    (hCurrent : output.current ≠ none) :
    evalConfigWithin program (state input output) 6 =
      PMF.pure (state input.moveRight
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
one actual input cell while preserving every output bit. -/
theorem eval_columns (columns : List BinaryModularAddition.Column)
    (skipped tail : List Bool)
    (hLength : skipped.length = columns.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state
        { Tape.ofBits (skipped ++ tail) with left := beforeInput }
        { Tape.ofBits (BinaryModularAddition.interleave columns) with
          left := beforeOutput })
      (6 * columns.length + 2) =
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
      obtain ⟨a, suffix, hSkipped⟩ :
          ∃ a suffix, skipped = a :: suffix := by
        cases skipped with
        | nil => simp at hLength
        | cons a suffix => exact ⟨a, suffix, rfl⟩
      subst skipped
      have hRest : suffix.length = rest.length := by
        simp at hLength
        omega
      rcases column with ⟨⟨first, second⟩, modulus⟩
      have hCurrent :
          ({ Tape.ofBits (BinaryModularAddition.interleave
              (((first, second), modulus) :: rest)) with
              left := beforeOutput } : Tape).current ≠ none := by
        simp [BinaryModularAddition.interleave, Tape.ofBits]
      have hInputStep :
          ({ Tape.ofBits ((a :: suffix) ++ tail) with
            left := beforeInput } : Tape).moveRight =
            { Tape.ofBits (suffix ++ tail) with
              left := [some a] ++ beforeInput } := by
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
      have hTime : 6 * (((first, second), modulus) :: rest).length + 2 =
          6 + (6 * rest.length + 2) := by simp; omega
      rw [hTime, evalConfigWithin_add]
      simp only [eval_step _ _ hCurrent, PMF.pure_bind,
        hInputStep, hOutputStep]
      convert ih suffix hRest
        ([some a] ++ beforeInput)
        ([some modulus, some second, some first] ++ beforeOutput) using 1;
        simp [BinaryModularAddition.interleave,
          List.reverse_cons,
          List.map_append, List.append_assoc]

/-- Advance over the fixed-width generator field after the exponent has
been copied, retaining the prepared arithmetic tracks and the response frame. -/
theorem eval_generator (first exponent modulus generator reply : List Bool)
    (hFirst : first.length = modulus.length)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state { Tape.ofBits (generator ++ reply) with left := beforeInput }
        { Tape.ofBits (BinaryColumnSlotFill.fullSlots first exponent modulus) with
          left := beforeOutput })
      (6 * modulus.length + 2) =
      PMF.pure (finish
        { Tape.ofBits reply with left := generator.reverse.map some ++ beforeInput }
        { left := (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some ++
            beforeOutput }) := by
  have hLength : ((first.zip exponent).zip modulus).length = modulus.length := by
    simp [List.length_zip, hFirst, hExponent]
  simpa only [BinaryColumnSlotFill.fullSlots, hLength] using
    eval_columns ((first.zip exponent).zip modulus) generator reply
      (by simpa only [hLength] using hGenerator) beforeInput beforeOutput

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
        (6 * (output.right.length + 1) + 2) = PMF.pure target ∧
      target.halted = true := by
  suffices hAux : ∀ n (input output : Tape), output.right.length = n →
      ∃ target,
        evalConfigWithin program (state input output) (6 * (n + 1) + 2) =
          PMF.pure target ∧ target.halted = true from
    hAux output.right.length input output rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro input output hLength
      by_cases hCurrent : output.current = none
      · refine ⟨finish input output, ?_, rfl⟩
        have h := eval_end input output hCurrent
        simpa only [show 6 * (n + 1) + 2 = 2 + 6 * (n + 1) by omega] using
          eval_extend h rfl (6 * (n + 1))
      · let nextInput := input.moveRight
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
          have hTime : 6 * (n + 1) + 2 = 6 + 2 := by omega
          rw [hTime, evalConfigWithin_add,
            eval_step input output hCurrent, PMF.pure_bind]
          exact eval_end nextInput nextOutput hNext
        · have hLess : nextOutput.right.length < n := by
            simpa only [nextOutput, ← hLength] using
              right_length_lt output hCurrent hRight
          obtain ⟨target, hEval, hHalted⟩ :=
            ih nextOutput.right.length hLess nextInput nextOutput rfl
          refine ⟨target, ?_, hHalted⟩
          have hLe : 6 + (6 * (nextOutput.right.length + 1) + 2) ≤
              6 * (n + 1) + 2 := by omega
          have hTime : 6 * (n + 1) + 2 =
              (6 + (6 * (nextOutput.right.length + 1) + 2)) +
                ((6 * (n + 1) + 2) -
                  (6 + (6 * (nextOutput.right.length + 1) + 2))) := by omega
          rw [hTime]
          apply eval_extend _ hHalted _
          rw [evalConfigWithin_add,
            eval_step input output hCurrent, PMF.pure_bind]
          exact hEval

/-- The same finite code can be linked into a caller with arbitrary finite
physical tape contents; the unread output suffix bounds its loop count. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 6 * (output.right.length + 1) + 2 ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  obtain ⟨target, hEval, hHalt⟩ := all_context input output
  have hSupport : target ∈
      (evalConfigWithin program (state input output)
        (6 * (output.right.length + 1) + 2)).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨target, used, hUsed, run, hHalt⟩

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits 8 := by
  obtain ⟨target, hEval, hHalted⟩ := all_context (Tape.ofBits bits) ({} : Tape)
  apply haltsWithin_of_no_timeout_support program bits _
  unfold evalWithin
  have hInitial : Configuration.initial bits = state (Tape.ofBits bits) ({} : Tape) := rfl
  rw [hInitial]
  have hEval' : evalConfigWithin program (state (Tape.ofBits bits) ({} : Tape)) 8 =
      PMF.pure target := by simpa using hEval
  rw [hEval', PMF.pure_map]
  simp [hHalted]

theorem polynomialTime : PolynomialTime program := by
  exact ⟨fun _ => 8, PolynomiallyBounded.const 8, haltsWithin⟩

end Machine.OneFieldColumnSkip
