import Foundation.Crypto.Semantics.Machine.FramedArithmeticPrefix
import Foundation.Crypto.Semantics.Machine.FramePayloadCopy
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedFirstOperandCopy

private def firstReturn : Nat := FramedArithmeticPrefix.program.length + 1
private def finalReturn : Nat := firstReturn + FramePayloadCopy.program.length + 1
private def pre : Program := FramedArithmeticPrefix.program.asSubroutine 0 firstReturn

/-- Consume the security parameter and instance frame, then copy the first
operand frame using finite bit-machine instructions. The second operand is
still on the input tape; this is a parser stage, not the group multiplier. -/
def program : Program :=
  Program.withSubroutine pre FramePayloadCopy.program [.halt] finalReturn

def budget (length : Nat) : Nat := 40 * (length + 1)

private theorem first_layout : program =
    Program.withSubroutine [] FramedArithmeticPrefix.program
      (FramePayloadCopy.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, pre, firstReturn, Program.withSubroutine,
    Program.asSubroutine_length]

private theorem second_layout : program =
    Program.withSubroutine pre FramePayloadCopy.program [.halt] finalReturn := by
  rfl

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    change (Program.withSubroutine pre FramePayloadCopy.program [.halt]
      finalReturn)[finalReturn]? = some .halt
    have hOffset : finalReturn = pre.length + FramePayloadCopy.program.length + 1 + 0 := by
      simp [finalReturn, firstReturn, pre, Program.asSubroutine_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

private theorem prefix_runs_frontier (bits : List Bool) :
    ∃ target used left rest beforeOutput blanks,
      used ≤ FramedArithmeticPrefix.budget bits.length ∧
      RunsFor FramedArithmeticPrefix.program
        (Configuration.initial bits) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits rest with left := left } ∧
      target.outputTape =
        { left := beforeOutput, right := List.replicate blanks none } ∧
      rest.length ≤ bits.length ∧
      (rest = [] ∨ beforeOutput = []) ∧
      (beforeOutput = [] ∨ ∃ count, beforeOutput = List.replicate count (some true)) := by
  obtain ⟨mid, u1, before, tail, hu1, hTail, run1, hHalt1, hInput1, hOutput1⟩ :=
    skipUnary_terminates_with_suffix [] bits {}
  obtain ⟨after, u2, left, rest, beforeOutput, blanks, hu2, run2,
    hHalt2, hInput2, hOutput2, hRest, hFrontier, hShape⟩ :=
    skipFrame_terminates_clean_or_empty before tail
  have hInitial :
      ({ inputTape := { Tape.ofBits bits with left := [] },
         outputTape := ({} : Tape) } : Configuration) = Configuration.initial bits := by
    cases bits <;> rfl
  rw [hInitial] at run1
  have hFirstLayout : FramedArithmeticPrefix.program =
      Program.withSubroutine [] skipUnary
        (skipFrame.asSubroutine 7 21 ++ [.halt]) 7 := by
    simp [FramedArithmeticPrefix.program, Program.withSubroutine]
  have hSecondLayout : FramedArithmeticPrefix.program =
      Program.withSubroutine (skipUnary.asSubroutine 0 7) skipFrame [.halt] 21 := by
    simp [FramedArithmeticPrefix.program, Program.withSubroutine, skipUnary]
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] skipUnary (skipFrame.asSubroutine 7 21 ++ [.halt]) 7
    (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor FramedArithmeticPrefix.program
      (Configuration.initial bits) (mid.resumeAt 7) v1 := by
    simpa only [← hFirstLayout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  have hMid : mid.resumeAt 7 =
      (({ inputTape := { Tape.ofBits tail with left := before },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7) := by
    simp [Configuration.resumeAt, Configuration.rebasePc, hInput1, hOutput1]
  rw [hMid] at r1
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    (skipUnary.asSubroutine 0 7) skipFrame [.halt] 21
    (Nat.zero_le _) rfl hHalt2
  have r2 : RunsFor FramedArithmeticPrefix.program
      (({ inputTape := { Tape.ofBits tail with left := before },
          outputTape := ({} : Tape) } : Configuration).rebasePc 7)
      (after.resumeAt 21) v2 := by
    simpa [hSecondLayout, Program.asSubroutine_length, skipUnary] using embedded2
  have hLast : Step FramedArithmeticPrefix.program (after.resumeAt 21)
      { after.resumeAt 21 with halted := true } := by
    have hLookup : FramedArithmeticPrefix.program[21]? = some .halt := by decide
    simp [Step, successors, next, Configuration.resumeAt, hLookup, Instruction.next]
  refine ⟨{ after.resumeAt 21 with halted := true }, v1 + v2 + 1,
    left, rest, beforeOutput, blanks, ?_, (r1.trans r2).succ hLast,
    rfl, ?_, ?_, ?_, hFrontier, hShape⟩
  · change v1 + v2 + 1 ≤ 13 * bits.length + 9
    omega
  · simpa [Configuration.resumeAt] using hInput2
  · simpa [Configuration.resumeAt] using hOutput2
  · omega

private theorem copy_blank_input (input output : Tape)
    (hBlank : input.current = none) :
    RunsFor FramePayloadCopy.program
      { inputTape := input, outputTape := output }
      { pc := 29, inputTape := input, outputTape := output, halted := true } 2 := by
  have hBranch : Step FramePayloadCopy.program
      { inputTape := input, outputTape := output }
      { pc := 29, inputTape := input, outputTape := output } := by
    simp [Step, successors, next, FramePayloadCopy.program, Instruction.next,
      Configuration.tape, hBlank]
  have hHalt : Step FramePayloadCopy.program
      { pc := 29, inputTape := input, outputTape := output }
      { pc := 29, inputTape := input, outputTape := output, halted := true } := by
    simp [Step, successors, next, FramePayloadCopy.program, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt

/-- The second parser starts on the exact input cells left by the first.
Its scratch tape may contain redundant blank cells; tape equivalence transfers
the trace without pretending those cells were erased by a free operation. -/
theorem runs_valid (n : Nat) (instanceBits first second rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second ++ rest
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits = first ∧
      target.outputTape.Equivalent
        { left := first.reverse.map some ++ [none] } ∧
      target.inputTape.Equivalent
        { Tape.ofBits (frame second ++ rest) with
          left := first.reverse.map some ++
            some false :: List.replicate first.length (some true) ++
              instanceBits.reverse.map some ++
                some false :: List.replicate instanceBits.length (some true) ++
                  some false :: List.replicate n (some true) } := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++
    frame first ++ frame second ++ rest
  let following := frame first ++ frame second ++ rest
  obtain ⟨afterPrefix, u1, hu1, run1, hHalt1, hInput1, hBlank1⟩ :=
    FramedArithmeticPrefix.runs_valid n instanceBits following
  let before : List (Option Bool) :=
    instanceBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
  have hInput : afterPrefix.inputTape =
      { Tape.ofBits (frame first ++ frame second ++ rest) with left := before } := by
    simpa [before, following] using hInput1
  obtain ⟨ideal, u2, hu2, run2, hHalt2, hInput2, hTape2, hOutput2⟩ :=
    FramePayloadCopy.runs_valid before first (frame second ++ rest)
  let actual : Configuration :=
    { inputTape := afterPrefix.inputTape, outputTape := afterPrefix.outputTape }
  have hEquivalent :
      ({ inputTape := { Tape.ofBits (frame first ++ (frame second ++ rest)) with
          left := before } } : Configuration).Equivalent actual := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [hInput]
      simpa only [List.append_assoc] using Tape.Equivalent.refl
        ({ Tape.ofBits (frame first ++ (frame second ++ rest)) with left := before } : Tape)
    · exact hBlank1.symm
  obtain ⟨afterCopy, runCopy, hCopyEquiv⟩ :=
    run2.exists_equivalent hEquivalent
  have hCopyHalt : afterCopy.halted = true := hCopyEquiv.2.1.symm.trans hHalt2
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedArithmeticPrefix.program
    (FramePayloadCopy.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (afterPrefix.resumeAt firstReturn) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw, following, List.append_assoc]
      using embedded1
  have hJoin : afterPrefix.resumeAt firstReturn = actual.rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actual]
  rw [hJoin] at r1
  obtain ⟨v2, hv2, embedded2⟩ := runCopy.withSubroutine_halted
    pre FramePayloadCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hCopyHalt
  have r2 : RunsFor program (actual.rebasePc firstReturn)
      (afterCopy.resumeAt finalReturn) v2 := by
    simpa [second_layout, pre, Program.asSubroutine_length, firstReturn]
      using embedded2
  have hFinal : Step program (afterCopy.resumeAt finalReturn)
      { afterCopy.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ afterCopy.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, ?_, (r1.trans r2).succ hFinal, rfl, ?_, ?_, ?_⟩
  · have hFirstLength : first.length ≤ raw.length := by
      simp [raw, frame, encodeSecurityParameter]
      omega
    change v1 + v2 + 1 ≤ 40 * (raw.length + 1)
    change u1 ≤ 13 * (encodeSecurityParameter n ++
      frame instanceBits ++ following).length + 9 at hu1
    have hPrefixLength : (encodeSecurityParameter n ++
      frame instanceBits ++ following).length = raw.length := by
      simp [raw, following, List.append_assoc]
    rw [hPrefixLength] at hu1
    omega
  · simpa [Configuration.resumeAt, Configuration.outputBits]
      using hCopyEquiv.outputBits.symm.trans hOutput2
  · simpa [Configuration.resumeAt, hTape2]
      using hCopyEquiv.2.2.2.symm
  · have hIdealInput : ideal.inputTape.Equivalent
        { Tape.ofBits (frame second ++ rest) with
          left := first.reverse.map some ++
            some false :: List.replicate first.length (some true) ++ before } := by
      rw [hInput2]
      exact Tape.Equivalent.refl _
    simpa [Configuration.resumeAt, before, List.append_assoc]
      using hCopyEquiv.2.2.1.symm.trans hIdealInput

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- The composed parser stops even when its unary prefix or either frame is
malformed. A dirty scratch counter can only occur when the prefix parser has
already exhausted the input; the payload copier then takes its blank-input
halt branch. -/
theorem runs_layout (bits : List Bool) :
    ∃ (target : Configuration) (used : Nat) (copied : List Bool),
      used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true ∧
      target.outputTape.Equivalent
        { left := copied.reverse.map some ++ [none] } ∧
      ∃ left rest, target.inputTape.Equivalent
        { Tape.ofBits rest with left := left } ∧ rest.length ≤ bits.length := by
  obtain ⟨afterPrefix, u1, left, rest, beforeOutput, blanks,
    hu1, run1, hHalt1, hInput, hOutput, hRest, hFrontier, hShape⟩ :=
    prefix_runs_frontier bits
  let actual : Configuration :=
    { inputTape := afterPrefix.inputTape, outputTape := afterPrefix.outputTape }
  have hSecond : ∃ (afterCopy : Configuration) (u2 : Nat) (copied : List Bool),
      u2 ≤ 23 * rest.length + 11 ∧
      RunsFor FramePayloadCopy.program actual afterCopy u2 ∧
      afterCopy.halted = true ∧
      afterCopy.outputTape.Equivalent
        { left := copied.reverse.map some ++ [none] } ∧
      ∃ left' rest', afterCopy.inputTape.Equivalent
        { Tape.ofBits rest' with left := left' } ∧ rest'.length ≤ rest.length := by
    rcases hFrontier with hEmpty | hClean
    · have hBlank : afterPrefix.inputTape.current = none := by
        rw [hInput, hEmpty]
        rfl
      let finish : Configuration :=
        { pc := 29, inputTape := afterPrefix.inputTape,
          outputTape := afterPrefix.outputTape, halted := true }
      rcases hShape with hNil | ⟨count, hCount⟩
      · refine ⟨finish, 2, [], ?_, ?_, rfl, ?_, ?_⟩
        · omega
        · simpa [actual, finish] using
            copy_blank_input afterPrefix.inputTape afterPrefix.outputTape hBlank
        · rw [hOutput, hNil]
          exact (Tape.blank_padding_equivalent [] blanks).trans
            (FramePayloadCopy.trailing_blank_equivalent [])
        · refine ⟨left, [], ?_, by simp⟩
          rw [hInput, hEmpty]
          exact Tape.Equivalent.refl _
      refine ⟨finish, 2, List.replicate count true, ?_, ?_, rfl, ?_, ?_⟩
      · omega
      · simpa [actual, finish] using
          copy_blank_input afterPrefix.inputTape afterPrefix.outputTape hBlank
      · rw [hOutput, hCount]
        have hBase := Tape.blank_padding_equivalent
          (List.replicate count (some true)) blanks
        have hTrailing := FramePayloadCopy.trailing_blank_equivalent
          (List.replicate count true)
        have hTrailing' :
            ({ left := List.replicate count (some true) } : Tape).Equivalent
              { left := (List.replicate count true).reverse.map some ++ [none] } := by
          simpa only [List.reverse_replicate, List.map_replicate] using hTrailing
        simpa only [List.reverse_replicate, List.map_replicate] using
          hBase.trans hTrailing'
      · refine ⟨left, [], ?_, by simp⟩
        rw [hInput, hEmpty]
        exact Tape.Equivalent.refl _
    · obtain ⟨ideal, u2, copied, hu2, run2, hHalt2, hOutput2,
        left', rest', hInput2, hRest2⟩ :=
        FramePayloadCopy.runs_any_from_layout left rest
      have hEq :
          ({ inputTape := { Tape.ofBits rest with left := left } } :
            Configuration).Equivalent actual := by
        refine ⟨rfl, rfl, ?_, ?_⟩
        · rw [hInput]
          exact Tape.Equivalent.refl _
        · rw [hOutput, hClean]
          exact (Tape.blank_padding_equivalent [] blanks).symm
      obtain ⟨afterCopy, runCopy, hCopyEq⟩ :=
        run2.exists_equivalent hEq
      refine ⟨afterCopy, u2, copied, hu2, runCopy, ?_, ?_, ?_⟩
      · exact hCopyEq.2.1.symm.trans hHalt2
      · exact hCopyEq.2.2.2.symm.trans hOutput2
      · exact ⟨left', rest', hCopyEq.2.2.1.symm.trans
          (by rw [hInput2]; exact Tape.Equivalent.refl _), hRest2⟩
  obtain ⟨afterCopy, u2, copied, hu2, run2, hHalt2, hOutput2,
    left', rest', hInput2, hRest2⟩ := hSecond
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedArithmeticPrefix.program
    (FramePayloadCopy.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial bits)
      (afterPrefix.resumeAt firstReturn) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  have hJoin : afterPrefix.resumeAt firstReturn = actual.rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actual]
  rw [hJoin] at r1
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    pre FramePayloadCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt2
  have r2 : RunsFor program (actual.rebasePc firstReturn)
      (afterCopy.resumeAt finalReturn) v2 := by
    simpa [second_layout, pre, Program.asSubroutine_length, firstReturn]
      using embedded2
  have hFinal : Step program (afterCopy.resumeAt finalReturn)
      { afterCopy.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ afterCopy.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, copied, ?_, (r1.trans r2).succ hFinal, rfl, ?_, ?_⟩
  · change v1 + v2 + 1 ≤ 40 * (bits.length + 1)
    change u1 ≤ 13 * bits.length + 9 at hu1
    omega
  · simpa [Configuration.resumeAt] using hOutput2
  · exact ⟨left', rest', by simpa [Configuration.resumeAt] using hInput2,
      hRest2.trans hRest⟩

theorem runs (bits : List Bool) :
    ∃ target used, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, hUsed, run, hHalt, _, _⟩ := runs_layout bits
  exact ⟨target, used, hUsed, run, hHalt⟩

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  exact (PolynomiallyBounded.const 40).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

/-- The evaluator returns the actual first element payload. The theorem uses
the trace and all-input stopping certificate of the same finite program. -/
theorem eval_valid (n : Nat) (instanceBits first second rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second ++ rest
    evalWithin program raw (budget raw.length) = PMF.pure (some first) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt, hOutput, _, _⟩ :=
    runs_valid n instanceBits first second rest
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

end Machine.FramedFirstOperandCopy
