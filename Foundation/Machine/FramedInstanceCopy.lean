import Foundation.Machine.FramePayloadCopy
import Foundation.Machine.UnaryInput

namespace Machine.FramedInstanceCopy

/-- Consume the unary security parameter, then copy the complete instance
frame payload. Both stages are fixed native instruction lists. The resulting
payload still requires a separate finite-code projection to its modulus. -/
def program : Program :=
  skipUnary.asSubroutine 0 7 ++ FramePayloadCopy.program.asSubroutine 7 38 ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] skipUnary
      (FramePayloadCopy.program.asSubroutine 7 38 ++ [.halt]) 7 := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine (skipUnary.asSubroutine 0 7)
      FramePayloadCopy.program [.halt] 38 := by
  simp [program, Program.withSubroutine, skipUnary]

def budget (length : Nat) : Nat := 26 * length + 15

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem final_step (c : Configuration) (hPc : c.pc = 38)
    (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[38]? = some .halt := by decide
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The second native stage reads the exact cells left by the first stage.
In particular, no mathematical reconstruction of the input tape is used. -/
theorem runs_valid (n : Nat) (instanceBits rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ rest
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := instanceBits.reverse.map some ++
            some false :: List.replicate instanceBits.length (some true) ++
              some false :: List.replicate n (some true) } ∧
      target.outputTape =
        { left := instanceBits.reverse.map some ++ [none] } ∧
      target.outputBits = instanceBits := by
  dsimp only
  let before : List (Option Bool) := some false :: List.replicate n (some true)
  let tail := frame instanceBits ++ rest
  have unary := skipUnary_runs [] n tail ({} : Tape)
  have hStart : skipUnaryStart [] n tail ({} : Tape) =
      Configuration.initial (encodeSecurityParameter n ++ tail) := by
    cases hBits : encodeSecurityParameter n ++ tail <;>
      simp [skipUnaryStart, Configuration.initial, Tape.ofBits, hBits]
  obtain ⟨v1, hv1, embed1⟩ := unary.withSubroutine_halted
    [] skipUnary (FramePayloadCopy.program.asSubroutine 7 38 ++ [.halt]) 7
    (Nat.zero_le _) rfl rfl
  have r1 : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ tail))
      ((skipUnaryFinish [] n tail ({} : Tape)).resumeAt 7) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, hStart] using embed1
  have copy := FramePayloadCopy.runs_valid before instanceBits rest
  obtain ⟨after, u2, hu2, run2, hAfter, hInput, hTape, hOutput⟩ := copy
  have hJoin : (skipUnaryFinish [] n tail ({} : Tape)).resumeAt 7 =
      (({ inputTape := { Tape.ofBits (frame instanceBits ++ rest) with
            left := before } } : Configuration).rebasePc 7) := by
    simp [skipUnaryFinish, Configuration.resumeAt, Configuration.rebasePc,
      before, tail]
  rw [hJoin] at r1
  obtain ⟨v2, hv2, embed2⟩ := run2.withSubroutine_halted
    (skipUnary.asSubroutine 0 7) FramePayloadCopy.program [.halt] 38
    (Nat.zero_le _) rfl hAfter
  have r2 : RunsFor program
      (({ inputTape := { Tape.ofBits (frame instanceBits ++ rest) with
            left := before } } : Configuration).rebasePc 7)
      (after.resumeAt 38) v2 := by
    simpa [second_layout, Program.asSubroutine_length, skipUnary] using embed2
  have last : Step program (after.resumeAt 38)
      { after.resumeAt 38 with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ after.resumeAt 38 with halted := true }, v1 + v2 + 1,
    ?_, ?_, rfl, ?_, ?_, ?_⟩
  · change v1 + v2 + 1 ≤
      26 * (encodeSecurityParameter n ++ frame instanceBits ++ rest).length + 15
    simp only [encodeSecurityParameter, frame, List.length_append,
      List.length_replicate, List.length_cons] at *
    omega
  · simpa only [tail, List.append_assoc] using (r1.trans r2).succ last
  · simpa [Configuration.resumeAt, before, List.append_assoc] using hInput
  · simpa [Configuration.resumeAt] using hTape
  · simpa [Configuration.resumeAt, Configuration.outputBits] using hOutput

/-- All finite inputs stop, including malformed unary headers and truncated
instance frames. The bound counts both native parsers and the final halt. -/
theorem runs (bits : List Bool) :
    ∃ target used, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true := by
  obtain ⟨mid, u1, left, rest, hu1, hrest, run1, hhalt1,
    hinput1, houtput1⟩ := skipUnary_terminates_with_suffix [] bits {}
  obtain ⟨after, u2, hu2, run2, hhalt2⟩ :=
    FramePayloadCopy.runs_any_from left rest
  have hInitial :
      ({ inputTape := { Tape.ofBits bits with left := [] },
         outputTape := ({} : Tape) } : Configuration) =
        Configuration.initial bits := by cases bits <;> rfl
  rw [hInitial] at run1
  obtain ⟨v1, hv1, embed1⟩ := run1.withSubroutine_halted
    [] skipUnary (FramePayloadCopy.program.asSubroutine 7 38 ++ [.halt]) 7
    (Nat.zero_le _) rfl hhalt1
  have r1 : RunsFor program (Configuration.initial bits) (mid.resumeAt 7) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embed1
  have hMid : mid.resumeAt 7 =
      (({ inputTape := { Tape.ofBits rest with left := left },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7) := by
    simp [Configuration.resumeAt, Configuration.rebasePc, hinput1, houtput1]
  rw [hMid] at r1
  obtain ⟨v2, hv2, embed2⟩ := run2.withSubroutine_halted
    (skipUnary.asSubroutine 0 7) FramePayloadCopy.program [.halt] 38
    (Nat.zero_le _) rfl hhalt2
  have r2 : RunsFor program
      (({ inputTape := { Tape.ofBits rest with left := left },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7)
      (after.resumeAt 38) v2 := by
    simpa [second_layout, Program.asSubroutine_length, skipUnary] using embed2
  have halt : Step program (after.resumeAt 38)
      { after.resumeAt 38 with halted := true } :=
    final_step _ rfl rfl
  refine ⟨_, v1 + v2 + 1, ?_, (r1.trans r2).succ halt, rfl⟩
  change v1 + v2 + 1 ≤ 26 * bits.length + 15
  omega

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem eval_valid (n : Nat) (instanceBits rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ rest
    evalWithin program raw (budget raw.length) =
      PMF.pure (some instanceBits) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt, _, _, hOutput⟩ :=
    runs_valid n instanceBits rest
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 26).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 15)

end Machine.FramedInstanceCopy
