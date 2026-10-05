import Foundation.Crypto.Semantics.Machine.ChooseFirstRangePreparation

set_option maxRecDepth 4096

namespace Machine.ChooseTwoRanges

private def compareEntry : Nat := ChooseFirstRangePreparation.program.length + 1
private def finalPc : Nat := compareEntry + DelimitedTapeComparison.program.length + 1

/-- The framed choose response is checked for both field widths and both
numeric ranges by one fixed list of machine instructions. -/
def program : Program :=
  ChooseFirstRangePreparation.program.asSubroutine 0 compareEntry ++
    DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseFirstRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseFirstRangePreparation.program.asSubroutine 0 compareEntry)
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
  9 * (length + ChooseFirstRangePreparation.budget length + 10) + 3

/-- Exact tape layout after both native comparisons. The first decision
occupies the first delimiter cell; the second decision remains at the
second delimiter cell, after its preserved marked payload. -/
theorem runs_both_ranges_layout (n width : Nat)
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
    let secondStatus :=
      BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
    let compared := DelimitedTapeComparison.done
      (BinaryComparison.compare Ordering.eq (first.zip modulus))
      ((DelimitedTapeComparison.marked first).reverse.map some ++
        some false :: before)
      (modulus.reverse.map some)
      (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent compared.inputTape ∧
      target.outputTape.Equivalent compared.outputTape := by
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
  let secondStatus :=
    BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
  let compared := DelimitedTapeComparison.done
    (BinaryComparison.compare Ordering.eq (first.zip modulus))
    ((DelimitedTapeComparison.marked first).reverse.map some ++ some false :: before)
    (modulus.reverse.map some)
    (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
  obtain ⟨prepared, used₁, preparedRun, hPreparedHalt,
    hPreparedInput, hPreparedOutput⟩ :=
    ChooseFirstRangePreparation.runs_matching_layout n width
      modulus suffix first second tail hModulus hInstance hFirst hSecond
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    preparedRun.withSubroutine_halted [] ChooseFirstRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry (Nat.zero_le _) rfl hPreparedHalt
  have firstRun : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt compareEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨used₂, _hUsed₂, comparisonRun⟩ :=
    DelimitedTapeComparison.runs_lt_layout (some false :: before) []
      first modulus (DelimitedTapeComparison.marked second ++ secondStatus :: tail)
      suffix (by omega)
  let expected := DelimitedTapeComparison.state Ordering.eq
    (some false :: before) []
    (FiniteBitEncoding.delimit first ++
      DelimitedTapeComparison.marked second ++ secondStatus :: tail)
    instanceBits
  have hEquivalent : (expected.rebasePc compareEntry).Equivalent
      (prepared.resumeAt compareEntry) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact hPreparedInput.symm
    · have hCanonical :
          (expected.rebasePc compareEntry).outputTape.Equivalent
            (Tape.ofBits instanceBits) := by
        cases hCode : instanceBits with
        | nil =>
            simp [Tape.Equivalent, expected, DelimitedTapeComparison.state,
              Configuration.rebasePc, instanceBits, hCode, Tape.ofBits]
        | cons bit rest =>
            simp [Tape.Equivalent, expected, DelimitedTapeComparison.state,
              Configuration.rebasePc, instanceBits, hCode, Tape.ofBits]
      exact hCanonical.trans hPreparedOutput.symm
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    comparisonRun.withSubroutine_halted
      (ChooseFirstRangePreparation.program.asSubroutine 0 compareEntry)
      DelimitedTapeComparison.program [.halt] finalPc
      (Nat.zero_le _) rfl rfl
  have secondRun : RunsFor program (expected.rebasePc compareEntry)
      (compared.resumeAt finalPc) returned₂ := by
    simpa [second_layout, compareEntry, Program.asSubroutine_length,
      Configuration.rebasePc, compared, expected, List.map_reverse,
      List.append_assoc] using embedded₂
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
    (firstRun.trans actualRun).succ hLast, rfl, ?_, ?_⟩
  · exact hActual.2.2.1.symm
  · exact hActual.2.2.2.symm

/-- The two delimiter cells carry precisely the two numerical range
decisions. The second status lies past the preserved marked second field. -/
theorem runs_both_ranges_decisions (n width : Nat)
    (modulus suffix first second tail : List Bool)
    (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let instanceBits := modulus ++ suffix
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.current =
        some (decide (Binary.value first < Binary.value modulus)) ∧
      target.inputTape.right.getD
        (DelimitedTapeComparison.marked second).length none =
        some (decide (Binary.value second < Binary.value modulus)) := by
  let instanceBits := modulus ++ suffix
  let reply := false :: FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ tail
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  let secondStatus :=
    BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
  let compared := DelimitedTapeComparison.done
    (BinaryComparison.compare Ordering.eq (first.zip modulus))
    ((DelimitedTapeComparison.marked first).reverse.map some ++ some false :: before)
    (modulus.reverse.map some)
    (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
  obtain ⟨target, used, run, hHalt, hInput, _⟩ :=
    runs_both_ranges_layout n width modulus suffix first second tail
      hModulus hInstance hFirst hSecond
  refine ⟨target, used, run, hHalt, ?_, ?_⟩
  · exact hInput.1.trans
      (DelimitedTapeComparison.done_lt_status (some false :: before) []
        first modulus
        (DelimitedTapeComparison.marked second ++ secondStatus :: tail)
        suffix (by omega))
  · have hSecondStatus : secondStatus =
        decide (Binary.value second < Binary.value modulus) := by
      have h := DelimitedTapeComparison.done_lt_status [] []
        second modulus [] [] (by omega)
      simpa [DelimitedTapeComparison.done, Tape.write, secondStatus] using h
    have hRight : compared.inputTape.right.getD
        (DelimitedTapeComparison.marked second).length none =
        some secondStatus := by
      simp [compared, DelimitedTapeComparison.done, Tape.write,
        Tape.ofBits, List.getD_append]
    exact (hInput.2.2 _).trans (hRight.trans (by rw [hSecondStatus]))

/-- Both comparisons and their tape rewinds halt on every finite input,
including malformed frames and incomplete candidate fields. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseFirstRangePreparation.runs_any raw
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseFirstRangePreparation.program
      (DelimitedTapeComparison.program.asSubroutine compareEntry finalPc ++ [.halt])
      compareEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt compareEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    DelimitedTapeComparison.runs_from_anyTape Ordering.eq
      after.inputTape after.outputTape
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseFirstRangePreparation.program.asSubroutine 0 compareEntry)
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

theorem budget_polynomial : PolynomiallyBounded budget := by
  have hFirst : PolynomiallyBounded ChooseFirstRangePreparation.budget := by
    unfold ChooseFirstRangePreparation.budget
    have hSecond : PolynomiallyBounded ChooseSecondRangeCheck.budget := by
      unfold ChooseSecondRangeCheck.budget
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
      exact ((PolynomiallyBounded.const 9).mul
        ((PolynomiallyBounded.id.add hPrepare).add
          (PolynomiallyBounded.const 10))).add
            (PolynomiallyBounded.const 3)
    exact ((PolynomiallyBounded.const 9).mul
      ((PolynomiallyBounded.id.add hSecond).add
        (PolynomiallyBounded.const 10))).add
          (PolynomiallyBounded.const 3)
  unfold budget
  exact ((PolynomiallyBounded.const 9).mul
    ((PolynomiallyBounded.id.add hFirst).add
      (PolynomiallyBounded.const 10))).add
        (PolynomiallyBounded.const 3)

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomial, haltsWithin⟩

/-- The operational layout theorem holds at the program's public
polynomial budget, not merely at an existential stopping time. -/
theorem eval_both_ranges_layout (n width : Nat)
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
    let secondStatus :=
      BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
    let compared := DelimitedTapeComparison.done
      (BinaryComparison.compare Ordering.eq (first.zip modulus))
      ((DelimitedTapeComparison.marked first).reverse.map some ++
        some false :: before)
      (modulus.reverse.map some)
      (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
    ∃ target,
      evalConfigWithin program (Configuration.initial raw)
        (budget raw.length) = PMF.pure target ∧
      target.halted = true ∧
      target.inputTape.Equivalent compared.inputTape ∧
      target.outputTape.Equivalent compared.outputTape := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++
    frame (false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail)
  obtain ⟨layout, layoutUsed, layoutRun, hLayoutHalt,
    hInput, hOutput⟩ :=
    runs_both_ranges_layout n width modulus suffix first second tail
      hModulus hInstance hFirst hSecond
  obtain ⟨bounded, used, hUsed, boundedRun, hBoundedHalt⟩ := runs_any raw
  have hSame : layout = bounded :=
    layoutRun.halted_finish_eq_of_no_randomBit boundedRun
      hLayoutHalt hBoundedHalt no_randomBit
  have hAll := boundedRun.haltsFrom_of_no_randomBit
    hBoundedHalt no_randomBit (Nat.le_refl used)
  have hEval : evalConfigWithin program (Configuration.initial raw)
      (budget raw.length) = PMF.pure bounded := by
    exact (evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll).trans
      (boundedRun.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit)
  refine ⟨bounded, ?_, hBoundedHalt, ?_, ?_⟩
  · simpa [raw] using hEval
  · simpa [hSame, raw] using hInput
  · simpa [hSame, raw] using hOutput

end Machine.ChooseTwoRanges
