import Foundation.Machine.UnaryInput
import Foundation.Machine.FramedInput

namespace Machine.FramedArithmeticPrefix

/-- Consume the unary security parameter and the instance frame by actual
machine transitions. On a valid request, the input head reaches the first
element frame. This routine does not extract or interleave arithmetic fields. -/
def program : Program :=
  skipUnary.asSubroutine 0 7 ++ skipFrame.asSubroutine 7 21 ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] skipUnary
      (skipFrame.asSubroutine 7 21 ++ [.halt]) 7 := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine (skipUnary.asSubroutine 0 7) skipFrame [.halt] 21 := by
  simp [program, Program.withSubroutine, skipUnary]

def budget (length : Nat) : Nat := 13 * length + 9

private theorem final_step (c : Configuration) (hPc : c.pc = 21)
    (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[21]? = some .halt := by
    decide
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- Every finite input, including malformed unary headers and truncated
frames, stops within a linear bound. -/
theorem runs (bits : List Bool) :
    ∃ target used, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true := by
  obtain ⟨mid, u1, left, rest, hu1, hrest, run1, hhalt1, hinput1, houtput1⟩ :=
    skipUnary_terminates_with_suffix [] bits {}
  obtain ⟨after, u2, hu2, run2, hhalt2⟩ :=
    skipFrame_terminates_from left rest
  have hInitial :
      ({ inputTape := { Tape.ofBits bits with left := [] },
         outputTape := ({} : Tape) } : Configuration) = Configuration.initial bits := by
    cases bits <;> rfl
  rw [hInitial] at run1
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] skipUnary (skipFrame.asSubroutine 7 21 ++ [.halt]) 7
    (Nat.zero_le _) rfl hhalt1
  have r1 : RunsFor program (Configuration.initial bits) (mid.resumeAt 7) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  have hMid : mid.resumeAt 7 =
      (({ inputTape := { Tape.ofBits rest with left := left },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7) := by
    simp [Configuration.resumeAt, Configuration.rebasePc, hinput1, houtput1]
  rw [hMid] at r1
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    (skipUnary.asSubroutine 0 7) skipFrame [.halt] 21
    (Nat.zero_le _) rfl hhalt2
  have r2 : RunsFor program
      (({ inputTape := { Tape.ofBits rest with left := left },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7)
      (after.resumeAt 21) v2 := by
    simpa [second_layout, Program.asSubroutine_length, skipUnary] using embedded2
  have halt : Step program (after.resumeAt 21)
      { after.resumeAt 21 with halted := true } :=
    final_step _ rfl rfl
  refine ⟨_, v1 + v2 + 1, ?_, (r1.trans r2).succ halt, rfl⟩
  change v1 + v2 + 1 ≤ 13 * bits.length + 9
  omega

/-- On a valid public prefix, the input head is physically positioned at
the first element frame. The instance frame has been consumed, not decoded
or copied into the arithmetic engine. -/
theorem runs_valid (n : Nat) (instanceBits rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ rest
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := instanceBits.reverse.map some ++
            some false :: (List.replicate instanceBits.length (some true) ++
              some false :: List.replicate n (some true)) } ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let savedPrefix : List (Option Bool) := some false :: List.replicate n (some true)
  let tail := frame instanceBits ++ rest
  have run1 := skipUnary_runs [] n tail ({} : Tape)
  obtain ⟨v1, hv1, embed1⟩ := run1.withSubroutine_halted
    [] skipUnary (skipFrame.asSubroutine 7 21 ++ [.halt]) 7
    (Nat.zero_le _) rfl rfl
  have hStart : skipUnaryStart [] n tail ({} : Tape) =
      Configuration.initial (encodeSecurityParameter n ++ tail) := by
    cases hBits : encodeSecurityParameter n ++ tail <;>
      simp [skipUnaryStart, Configuration.initial, Tape.ofBits, hBits]
  have r1 : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ tail))
      ((skipUnaryFinish [] n tail ({} : Tape)).resumeAt 7) v1 := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil,
      Nat.zero_add, hStart] using embed1
  have hMid : (skipUnaryFinish [] n tail ({} : Tape)).resumeAt 7 =
      (skipFrameStart instanceBits.length (instanceBits ++ rest) savedPrefix).rebasePc 7 := by
    simp [skipUnaryFinish, skipFrameStart, savedPrefix, tail, frame,
      Configuration.resumeAt, Configuration.rebasePc, List.append_assoc]
  rw [hMid] at r1
  have run2 := skipFrame_runs_from savedPrefix instanceBits.length (instanceBits ++ rest)
  obtain ⟨v2, hv2, embed2⟩ := run2.withSubroutine_halted
    (skipUnary.asSubroutine 0 7) skipFrame [.halt] 21
    (Nat.zero_le _) rfl rfl
  have r2 : RunsFor program
      ((skipFrameStart instanceBits.length (instanceBits ++ rest) savedPrefix).rebasePc 7)
      ((skipFrameFinish instanceBits.length (instanceBits ++ rest) savedPrefix).resumeAt 21) v2 := by
    simpa [second_layout, Program.asSubroutine_length, skipUnary] using embed2
  let after := skipFrameFinish instanceBits.length (instanceBits ++ rest) savedPrefix
  have last : Step program (after.resumeAt 21)
      { after.resumeAt 21 with halted := true } :=
    final_step _ rfl rfl
  have hTape : after.inputTape =
      { Tape.ofBits rest with
        left := instanceBits.reverse.map some ++
          some false :: (List.replicate instanceBits.length (some true) ++
            some false :: List.replicate n (some true)) } := by
    simpa only [after, savedPrefix] using
      skipFrameFinish_input instanceBits rest savedPrefix
  have hBlank : after.outputTape.Equivalent ({} : Tape) :=
    skipFrameFinish_output_blank instanceBits.length (instanceBits ++ rest) savedPrefix
  refine ⟨{ after.resumeAt 21 with halted := true }, v1 + v2 + 1,
    ?_, ?_, rfl, ?_, ?_⟩
  · change v1 + v2 + 1 ≤
      13 * (encodeSecurityParameter n ++ frame instanceBits ++ rest).length + 9
    simp only [encodeSecurityParameter, frame, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  · simpa only [tail, List.append_assoc] using (r1.trans r2).succ last
  · simpa [Configuration.resumeAt] using hTape
  · simpa [Configuration.resumeAt] using hBlank

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨target, used, hu, run, hh⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hh no_randomBit hu

/-- The evaluator observes the same physical frontier at the certified
budget. This form can be composed with a later finite frame extractor. -/
theorem eval_valid (n : Nat) (instanceBits rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ rest
    ∃ target,
      evalConfigWithin program (Configuration.initial raw) (budget raw.length) =
        PMF.pure target ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := instanceBits.reverse.map some ++
            some false :: (List.replicate instanceBits.length (some true) ++
              some false :: List.replicate n (some true)) } ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalted, hInput, hOutput⟩ :=
    runs_valid n instanceBits rest
  refine ⟨target, ?_, hHalted, hInput, hOutput⟩
  have hAll := run.haltsFrom_of_no_randomBit hHalted no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 13).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 9)

end Machine.FramedArithmeticPrefix
