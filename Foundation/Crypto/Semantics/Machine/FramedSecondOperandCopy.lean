import Foundation.Crypto.Semantics.Machine.FramedFirstOperandCopy
import Foundation.Crypto.Semantics.Machine.BitstringErasure
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedSecondOperandCopy

private def firstReturn : Nat := FramedFirstOperandCopy.program.length + 1
private def secondReturn : Nat := firstReturn + eraseOutputBlock.length + 1
private def finalReturn : Nat := secondReturn + FramePayloadCopy.program.length + 1
private def first : Program := FramedFirstOperandCopy.program.asSubroutine 0 firstReturn
private def second : Program := eraseOutputBlock.asSubroutine firstReturn secondReturn

/-- A fixed code reads the first element frame, erases its scratch copy with
charged bit transitions, and reads the second element frame. The first value
remains on the unchanged input tape; this stage does not yet interleave the
three operands for the arithmetic engine. -/
def program : Program :=
  first ++ second ++ FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt]

def budget (length : Nat) : Nat := 400 * (length + 1)

private theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem first_layout : program =
    Program.withSubroutine [] FramedFirstOperandCopy.program
      (second ++ FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
      firstReturn := by
  simp only [program, first, Program.withSubroutine, List.length_nil, List.nil_append,
    List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first eraseOutputBlock
      (FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
      secondReturn := by
  have hLen : first.length = firstReturn := by
    simp [first, firstReturn, Program.asSubroutine_length]
  simp only [program, second, Program.withSubroutine, hLen, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) FramePayloadCopy.program [.halt]
      finalReturn := by
  rfl

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [third_layout]
    have hOffset : finalReturn = (first ++ second).length +
        FramePayloadCopy.program.length + 1 + 0 := by
      simp [finalReturn, secondReturn, firstReturn, first, second,
        Program.asSubroutine_length]
      omega
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- On valid frames, both parser calls and the intervening erasure use the
same physical tapes. Tape equivalence only ignores redundant stored blanks;
it never reconstructs an operand from a Lean list as a machine action. -/
theorem runs_valid (n : Nat) (instanceBits firstBits secondBits rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame firstBits ++ frame secondBits ++ rest
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits = secondBits ∧
      target.inputTape.Equivalent
        { Tape.ofBits rest with
          left := secondBits.reverse.map some ++
            some false :: List.replicate secondBits.length (some true) ++
              firstBits.reverse.map some ++
                some false :: List.replicate firstBits.length (some true) ++
                  instanceBits.reverse.map some ++
                    some false :: List.replicate instanceBits.length (some true) ++
                      some false :: List.replicate n (some true) } := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++
    frame firstBits ++ frame secondBits ++ rest
  let before : List (Option Bool) :=
    firstBits.reverse.map some ++
      some false :: List.replicate firstBits.length (some true) ++
        instanceBits.reverse.map some ++
          some false :: List.replicate instanceBits.length (some true) ++
            some false :: List.replicate n (some true)
  obtain ⟨afterFirst, u1, hu1, run1, hHalt1, _, hOutput1, hInput1⟩ :=
    FramedFirstOperandCopy.runs_valid n instanceBits firstBits secondBits rest
  let actualErase : Configuration :=
    { inputTape := afterFirst.inputTape, outputTape := afterFirst.outputTape }
  have hEraseStart : (eraseOutputBlockStart afterFirst.inputTape [] firstBits []).Equivalent
      actualErase := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    change ({ left := firstBits.reverse.map some ++ [none] } : Tape).Equivalent
      afterFirst.outputTape
    simpa [List.map_reverse] using hOutput1.symm
  obtain ⟨afterErase, runErase, hEraseEquiv⟩ :=
    (eraseOutputBlock_runs afterFirst.inputTape [] firstBits []).exists_equivalent
      hEraseStart
  have hEraseHalt : afterErase.halted = true := hEraseEquiv.2.1.symm.trans rfl
  have hEraseInput : afterErase.inputTape.Equivalent
      { Tape.ofBits (frame secondBits ++ rest) with left := before } := by
    have hActualInput : afterErase.inputTape.Equivalent afterFirst.inputTape :=
      hEraseEquiv.2.2.1.symm
    exact hActualInput.trans (by simpa [before, List.append_assoc] using hInput1)
  have hEraseBlank : afterErase.outputTape.Equivalent ({} : Tape) := by
    have hIdeal := hEraseEquiv.2.2.2.symm
    have hBlank : (eraseOutputBlockFinish afterFirst.inputTape [] firstBits []).outputTape.Equivalent
        ({} : Tape) := by
      change ({ right := List.replicate (firstBits.reverse.length + 1) none ++ [] } : Tape).Equivalent
        ({} : Tape)
      simpa only [List.length_reverse, List.append_nil] using
        Tape.blank_padding_equivalent [] (firstBits.length + 1)
    exact hIdeal.trans hBlank
  let actualCopy : Configuration :=
    { inputTape := afterErase.inputTape, outputTape := afterErase.outputTape }
  have hCopyStart :
      ({ inputTape := { Tape.ofBits (frame secondBits ++ rest) with left := before } } :
        Configuration).Equivalent actualCopy :=
    ⟨rfl, rfl, hEraseInput.symm, hEraseBlank.symm⟩
  obtain ⟨idealCopy, u3, hu3, run3, hHalt3, hInput3, _, hOutput3⟩ :=
    FramePayloadCopy.runs_valid before secondBits rest
  obtain ⟨afterCopy, runCopy, hCopyEquiv⟩ :=
    run3.exists_equivalent hCopyStart
  have hCopyHalt : afterCopy.halted = true := hCopyEquiv.2.1.symm.trans hHalt3
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedFirstOperandCopy.program
    (second ++ FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (afterFirst.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add,
      raw, List.append_assoc] using embedded1
  have hJoin1 : afterFirst.resumeAt firstReturn = actualErase.rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actualErase]
  rw [hJoin1] at r1
  obtain ⟨v2, hv2, embedded2⟩ := runErase.withSubroutine_halted
    first eraseOutputBlock
    (FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hEraseHalt
  have r2 : RunsFor program (actualErase.rebasePc firstReturn)
      (afterErase.resumeAt secondReturn) v2 := by
    simpa [second_layout, first, Program.asSubroutine_length, firstReturn]
      using embedded2
  have hJoin2 : afterErase.resumeAt secondReturn = actualCopy.rebasePc secondReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actualCopy,
      secondReturn, firstReturn]
  rw [hJoin2] at r2
  obtain ⟨v3, hv3, embedded3⟩ := runCopy.withSubroutine_halted
    (first ++ second) FramePayloadCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hCopyHalt
  have r3 : RunsFor program (actualCopy.rebasePc secondReturn)
      (afterCopy.resumeAt finalReturn) v3 := by
    have hOffset : (first ++ second).length = secondReturn := by
      simp [secondReturn, firstReturn, first, second, Program.asSubroutine_length]
      omega
    rw [hOffset] at embedded3
    simpa only [← third_layout] using embedded3
  have hFinal : Step program (afterCopy.resumeAt finalReturn)
      { afterCopy.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ afterCopy.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, ?_, ((r1.trans r2).trans r3).succ hFinal, rfl, ?_, ?_⟩
  · have hFirstLength : firstBits.length ≤ raw.length := by
      simp [raw, frame, encodeSecurityParameter]
      omega
    have hSecondLength : secondBits.length ≤ raw.length := by
      simp [raw, frame, encodeSecurityParameter]
      omega
    change v1 + v2 + v3 + 1 ≤ 400 * (raw.length + 1)
    change u1 ≤ 40 * raw.length + 40 at hu1
    omega
  · simpa [Configuration.resumeAt, Configuration.outputBits]
      using hCopyEquiv.outputBits.symm.trans hOutput3
  · have hActualInput : afterCopy.inputTape.Equivalent idealCopy.inputTape :=
      hCopyEquiv.2.2.1.symm
    simpa [Configuration.resumeAt, hInput3, before, List.append_assoc]
      using hActualInput

/-- The parser also stops on malformed finite requests. The first parser's
all-input frontier records the actual copied output block and unread input
suffix; erasure and the second copy run on those physical tapes. -/
theorem runs (bits : List Bool) :
    ∃ target used, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true := by
  obtain ⟨afterFirst, u1, copied, hu1, run1, hHalt1, hOutput1,
    left, rest, hInput1, hRest⟩ := FramedFirstOperandCopy.runs_layout bits
  let actualErase : Configuration :=
    { inputTape := afterFirst.inputTape, outputTape := afterFirst.outputTape }
  have hEraseStart :
      (eraseOutputBlockStart afterFirst.inputTape [] copied []).Equivalent actualErase := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    change ({ left := copied.reverse.map some ++ [none] } : Tape).Equivalent
      afterFirst.outputTape
    exact hOutput1.symm
  obtain ⟨afterErase, runErase, hEraseEquiv⟩ :=
    (eraseOutputBlock_runs afterFirst.inputTape [] copied []).exists_equivalent
      hEraseStart
  have hEraseHalt : afterErase.halted = true := hEraseEquiv.2.1.symm.trans rfl
  have hEraseInput : afterErase.inputTape.Equivalent
      { Tape.ofBits rest with left := left } :=
    hEraseEquiv.2.2.1.symm.trans hInput1
  have hEraseBlank : afterErase.outputTape.Equivalent ({} : Tape) := by
    have hIdeal :
        (eraseOutputBlockFinish afterFirst.inputTape [] copied []).outputTape.Equivalent
          ({} : Tape) := by
      change ({ right := List.replicate (copied.reverse.length + 1) none ++ [] } : Tape).Equivalent
        ({} : Tape)
      simpa only [List.length_reverse, List.append_nil] using
        Tape.blank_padding_equivalent [] (copied.length + 1)
    exact hEraseEquiv.2.2.2.symm.trans hIdeal
  let actualCopy : Configuration :=
    { inputTape := afterErase.inputTape, outputTape := afterErase.outputTape }
  have hCopyStart :
      ({ inputTape := { Tape.ofBits rest with left := left } } :
        Configuration).Equivalent actualCopy :=
    ⟨rfl, rfl, hEraseInput.symm, hEraseBlank.symm⟩
  obtain ⟨idealCopy, u3, hu3, run3, hHalt3⟩ :=
    FramePayloadCopy.runs_any_from left rest
  obtain ⟨afterCopy, runCopy, hCopyEquiv⟩ :=
    run3.exists_equivalent hCopyStart
  have hCopyHalt : afterCopy.halted = true := hCopyEquiv.2.1.symm.trans hHalt3
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedFirstOperandCopy.program
    (second ++ FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial bits)
      (afterFirst.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  have hJoin1 : afterFirst.resumeAt firstReturn = actualErase.rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actualErase]
  rw [hJoin1] at r1
  obtain ⟨v2, hv2, embedded2⟩ := runErase.withSubroutine_halted
    first eraseOutputBlock
    (FramePayloadCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hEraseHalt
  have r2 : RunsFor program (actualErase.rebasePc firstReturn)
      (afterErase.resumeAt secondReturn) v2 := by
    simpa [second_layout, first, Program.asSubroutine_length, firstReturn]
      using embedded2
  have hJoin2 : afterErase.resumeAt secondReturn = actualCopy.rebasePc secondReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, actualCopy,
      secondReturn, firstReturn]
  rw [hJoin2] at r2
  obtain ⟨v3, hv3, embedded3⟩ := runCopy.withSubroutine_halted
    (first ++ second) FramePayloadCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hCopyHalt
  have r3 : RunsFor program (actualCopy.rebasePc secondReturn)
      (afterCopy.resumeAt finalReturn) v3 := by
    have hOffset : (first ++ second).length = secondReturn := by
      simp [secondReturn, firstReturn, first, second, Program.asSubroutine_length]
      omega
    rw [hOffset] at embedded3
    simpa only [← third_layout] using embedded3
  have hFinal : Step program (afterCopy.resumeAt finalReturn)
      { afterCopy.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hCopiedBits : afterFirst.outputBits = copied := by
    have h := hOutput1.bits
    simpa [Configuration.outputBits, Tape.bits, List.reverse_append,
      List.map_reverse] using h
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run1
  have hInitial : (Configuration.initial bits).inputTape.cells +
      (Configuration.initial bits).outputTape.cells ≤ bits.length + 2 := by
    cases bits <;> simp [Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  have hCopiedLe : copied.length ≤ bits.length + 2 + u1 := by
    have hCells : afterFirst.outputTape.cells ≤ bits.length + 2 + u1 := by
      have hBound := hStorage.trans (Nat.add_le_add_right hInitial u1)
      simpa [GuardedCompiler.sourceStorage] using
        (Nat.le_add_left afterFirst.outputTape.cells afterFirst.inputTape.cells).trans hBound
    have hBits := afterFirst.outputTape.bits_length_le_cells
    rw [← hCopiedBits] at *
    exact hBits.trans hCells
  refine ⟨{ afterCopy.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, ?_, ((r1.trans r2).trans r3).succ hFinal, rfl⟩
  change v1 + v2 + v3 + 1 ≤ 400 * (bits.length + 1)
  change u1 ≤ 40 * (bits.length + 1) at hu1
  omega

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  exact (PolynomiallyBounded.const 400).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

/-- The same finite code returns the second payload on a valid framed
request. The first payload is erased by charged transitions before copying
the second; no output-tape reset is assumed. -/
theorem eval_valid (n : Nat) (instanceBits first second rest : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second ++ rest
    evalWithin program raw (budget raw.length) = PMF.pure (some second) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt, hOutput, _⟩ :=
    runs_valid n instanceBits first second rest
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

end Machine.FramedSecondOperandCopy
