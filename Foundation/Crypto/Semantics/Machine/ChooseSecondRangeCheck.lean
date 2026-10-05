import Foundation.Crypto.Semantics.Machine.ChooseRangePreparation

set_option maxRecDepth 4096

namespace Machine.ChooseSecondRangeCheck

private def compareEntry : Nat := ChooseRangePreparation.program.length + 1
private def finalPc : Nat := compareEntry + DelimitedTapeComparison.program.length + 1

/-- The framed choose prefix, both width scans, the charged rewind, and a
two-tape numerical comparison form one fixed finite instruction list. -/
def program : Program :=
  ChooseRangePreparation.program.asSubroutine 0 compareEntry ++
    DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseRangePreparation.program.asSubroutine 0 compareEntry)
      DelimitedTapeComparison.program [.halt] finalPc := by
  simp [program, Program.withSubroutine, compareEntry,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt,
    hLookup, Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat :=
  9 * (length + ChooseRangePreparation.budget length + 10) + 3

/-- On a well-framed, width-matching choose reply, the same physical
program decides whether the second candidate is below the stored modulus.
The first candidate and trailing state are retained in the input tape. -/
theorem runs_second_range (n width : Nat)
    (modulus suffix first second tail : List Bool)
    (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let instanceBits := modulus ++ suffix
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let before := some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
    let beforeSecond := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: before
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.current =
        some (decide (Binary.value second < Binary.value modulus)) ∧
      target.inputTape.Equivalent
        (DelimitedTapeComparison.done
          (BinaryComparison.compare Ordering.eq (second.zip modulus))
          ((DelimitedTapeComparison.marked second).reverse.map some ++ beforeSecond)
          (modulus.reverse.map some) tail suffix).inputTape ∧
      target.outputTape.Equivalent
        (DelimitedTapeComparison.done
          (BinaryComparison.compare Ordering.eq (second.zip modulus))
          ((DelimitedTapeComparison.marked second).reverse.map some ++ beforeSecond)
          (modulus.reverse.map some) tail suffix).outputTape := by
  dsimp only
  let instanceBits := modulus ++ suffix
  let reply := false :: FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  let beforeSecond : List (Option Bool) :=
    (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: before
  obtain ⟨prepared, used₁, preparedRun, hPreparedHalt,
    hPreparedInput, hPreparedOutput⟩ :=
    ChooseRangePreparation.runs_matching_layout n width
      instanceBits first second tail hInstance hFirst hSecond
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    preparedRun.withSubroutine_halted [] ChooseRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry (Nat.zero_le _) rfl hPreparedHalt
  have firstRun : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt compareEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨used₂, _hUsed₂, comparisonRun⟩ :=
    DelimitedTapeComparison.runs_lt_layout beforeSecond [] second modulus tail suffix
      (by omega)
  let compared := DelimitedTapeComparison.done
    (BinaryComparison.compare Ordering.eq (second.zip modulus))
    ((DelimitedTapeComparison.marked second).reverse.map some ++ beforeSecond)
    (modulus.reverse.map some) tail suffix
  have hComparedHalt : compared.halted = true := rfl
  have hStatus : compared.inputTape.current =
      some (decide (Binary.value second < Binary.value modulus)) :=
    DelimitedTapeComparison.done_lt_status beforeSecond []
      second modulus tail suffix (by omega)
  let expected := DelimitedTapeComparison.state Ordering.eq beforeSecond []
    (FiniteBitEncoding.delimit second ++ tail) instanceBits
  have hEquivalent : (expected.rebasePc compareEntry).Equivalent
      (prepared.resumeAt compareEntry) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact hPreparedInput.symm
    · have hCanonical :
          (expected.rebasePc compareEntry).outputTape.Equivalent
            (Tape.ofBits instanceBits) := by
        cases hCode : (modulus ++ suffix) with
        | nil =>
            simp [Tape.Equivalent, expected, DelimitedTapeComparison.state,
              Configuration.rebasePc, instanceBits, hCode, Tape.ofBits]
        | cons bit rest =>
            simp [Tape.Equivalent, expected, DelimitedTapeComparison.state,
              Configuration.rebasePc, instanceBits, hCode, Tape.ofBits]
      exact hCanonical.trans hPreparedOutput.symm
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    comparisonRun.withSubroutine_halted
      (ChooseRangePreparation.program.asSubroutine 0 compareEntry)
      DelimitedTapeComparison.program [.halt] finalPc
      (Nat.zero_le _) rfl hComparedHalt
  have secondRun : RunsFor program (expected.rebasePc compareEntry)
      (compared.resumeAt finalPc) returned₂ := by
    simpa [second_layout, compareEntry, Program.asSubroutine_length,
      Configuration.rebasePc, compared, List.map_reverse] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    secondRun.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalPc := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalPc]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_, ?_, ?_⟩
  · exact hActual.2.2.1.1.symm.trans hStatus
  · simpa only [compared, Configuration.resumeAt] using hActual.2.2.1.symm
  · simpa only [compared, Configuration.resumeAt] using hActual.2.2.2.symm

/-- The comparison stage also halts after malformed frames or truncated
candidate/modulus tapes; no validity premise enters this time bound. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseRangePreparation.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt compareEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    DelimitedTapeComparison.runs_from_anyTape Ordering.eq
      after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseRangePreparation.program.asSubroutine 0 compareEntry)
      DelimitedTapeComparison.program [.halt] finalPc
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt compareEntry)
      (finish.resumeAt finalPc) returned₂ := by
    have hEmbedded : RunsFor program
        ((DelimitedTapeComparison.atState Ordering.eq
          after.inputTape after.outputTape).rebasePc compareEntry)
        (finish.resumeAt finalPc) returned₂ := by
      simpa [second_layout, compareEntry, Program.asSubroutine_length,
        Configuration.rebasePc] using embedded₂
    have hStart :
        (DelimitedTapeComparison.atState Ordering.eq
          after.inputTape after.outputTape).rebasePc compareEntry =
            after.resumeAt compareEntry := by
      rw [DelimitedTapeComparison.atState_eq]
      rfl
    rw [hStart] at hEmbedded
    exact hEmbedded
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : Machine.GuardedCompiler.sourceStorage
      (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;>
      simp [Machine.GuardedCompiler.sourceStorage, Configuration.initial,
        Tape.cells, Tape.ofBits] <;> omega
  have hCells : after.inputTape.cells + after.outputTape.cells ≤
      raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage hInitial
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget] at *
    dsimp [Tape.cells] at hCells
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstRun.trans secondRun).succ (final_step finish), rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  have hPrepare : PolynomiallyBounded ChooseRangePreparation.budget := by
    unfold ChooseRangePreparation.budget
    have hPrefix : PolynomiallyBounded ChooseTwoWidthsPrefix.budget := by
      unfold ChooseTwoWidthsPrefix.budget
      exact ((PolynomiallyBounded.const 100000000000).mul
        ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
          (PolynomiallyBounded.const 100000000000)
    exact ((PolynomiallyBounded.const 9).mul
      ((PolynomiallyBounded.id.add hPrefix).add
        (PolynomiallyBounded.const 10))).add
          (PolynomiallyBounded.const 3)
  unfold budget
  exact ((PolynomiallyBounded.const 9).mul
    ((PolynomiallyBounded.id.add hPrepare).add
      (PolynomiallyBounded.const 10))).add
        (PolynomiallyBounded.const 3)

end Machine.ChooseSecondRangeCheck
