import Foundation.Crypto.Semantics.Machine.ChooseRangeStatusGate

set_option maxRecDepth 4096

namespace Machine.ChooseRangeValidation

private def gateEntry : Nat := ChooseTwoRanges.program.length + 1
private def finalPc : Nat := gateEntry + ChooseRangeStatusGate.program.length + 1

/-- Both comparisons and their native conjunction gate form one finite
instruction list. Width failure and subgroup membership are separate
acceptance conditions; this program is only the numeric-range stage. -/
def program : Program :=
  ChooseTwoRanges.program.asSubroutine 0 gateEntry ++
    ChooseRangeStatusGate.program.asSubroutine gateEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseTwoRanges.program
      (ChooseRangeStatusGate.program.asSubroutine gateEntry finalPc ++ [.halt])
      gateEntry := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseTwoRanges.program.asSubroutine 0 gateEntry)
      ChooseRangeStatusGate.program [.halt] finalPc := by
  simp [program, Program.withSubroutine, gateEntry,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat :=
  7 * (length + ChooseTwoRanges.budget length + 10) + 3

/-- The real range-comparison tapes are passed directly to the gate. Its
written status is the conjunction of the two numerical inequalities. -/
theorem runs_matching_layout (n width : Nat)
    (modulus suffix first second tail : List Bool)
    (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    let before := some false :: List.replicate reply.length (some true) ++
      (modulus ++ suffix).reverse.map some ++
        some false :: List.replicate (modulus ++ suffix).length (some true) ++
          some false :: List.replicate n (some true)
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputTape.left.getD 0 none =
        some (decide (Binary.value first < Binary.value modulus ∧
          Binary.value second < Binary.value modulus)) ∧
      target.inputTape.Equivalent
        { Tape.ofBits (false :: tail) with
          left := (DelimitedTapeComparison.marked second).reverse.map some ++
            some false :: ((DelimitedTapeComparison.marked first).reverse.map some ++
              some false :: before) } ∧
      target.outputTape.Equivalent
        (({ current := some (decide
          (Binary.value first < Binary.value modulus ∧ Binary.value second < Binary.value modulus)),
            right := modulus.map some ++ (Tape.ofBits suffix).current :: (Tape.ofBits suffix).right } : Tape).moveRight) := by
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
  let firstStatus :=
    BinaryComparison.compare Ordering.eq (first.zip modulus) == Ordering.lt
  let secondStatus :=
    BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
  let compared := DelimitedTapeComparison.done
    (BinaryComparison.compare Ordering.eq (first.zip modulus))
    ((DelimitedTapeComparison.marked first).reverse.map some ++ some false :: before)
    (modulus.reverse.map some)
    (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
  obtain ⟨after, used₁, run₁, hHalt₁, hInput, hOutput⟩ :=
    ChooseTwoRanges.runs_both_ranges_layout n width
      modulus suffix first second tail hModulus hInstance hFirst hSecond
  obtain ⟨returned₁, _, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseTwoRanges.program
      (ChooseRangeStatusGate.program.asSubroutine gateEntry finalPc ++ [.halt])
      gateEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt gateEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw, instanceBits] using embedded₁
  obtain ⟨finish, used₂, gateRun, hGateHalt, _, hStatus, hRestored, hRestoredOutput⟩ :=
    ChooseRangeStatusGate.runs_from_compared_layout
      (BinaryComparison.compare Ordering.eq (first.zip modulus))
      ((DelimitedTapeComparison.marked first).reverse.map some ++ some false :: before)
      modulus second tail suffix secondStatus (by omega)
  have hEquivalent :
      ((ChooseRangeStatusGate.entry compared.inputTape compared.outputTape).rebasePc
        gateEntry).Equivalent (after.resumeAt gateEntry) := by
    exact ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨returned₂, _, embedded₂⟩ :=
    gateRun.withSubroutine_halted
      (ChooseTwoRanges.program.asSubroutine 0 gateEntry)
      ChooseRangeStatusGate.program [.halt] finalPc
      (Nat.zero_le _) rfl hGateHalt
  have secondRun : RunsFor program
      ((ChooseRangeStatusGate.entry compared.inputTape compared.outputTape).rebasePc
        gateEntry) (finish.resumeAt finalPc) returned₂ := by
    simpa [second_layout, gateEntry, Program.asSubroutine_length,
      Configuration.rebasePc, compared] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ := secondRun.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalPc := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalPc]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt, hLookup, Instruction.next]
  have hFirstStatus : firstStatus =
      decide (Binary.value first < Binary.value modulus) := by
    simpa [firstStatus, DelimitedTapeComparison.done, Tape.write] using
      DelimitedTapeComparison.done_lt_status [] [] first modulus [] [] (by omega)
  have hSecondStatus : secondStatus =
      decide (Binary.value second < Binary.value modulus) := by
    simpa [secondStatus, DelimitedTapeComparison.done, Tape.write] using
      DelimitedTapeComparison.done_lt_status [] [] second modulus [] [] (by omega)
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_, ?_, ?_⟩
  · have hCell := (hActual.2.2.2.2.1 0).symm
    have hCombined : finish.outputTape.left.getD 0 none =
        some (decide (Binary.value first < Binary.value modulus ∧
          Binary.value second < Binary.value modulus)) := by
      change finish.outputTape.left.getD 0 none = some (firstStatus && secondStatus) at hStatus
      simpa [hFirstStatus, hSecondStatus] using hStatus
    exact hCell.trans hCombined
  · have h := hActual.2.2.1.symm
    change actual.inputTape.Equivalent finish.inputTape at h
    rw [hRestored] at h
    exact h
  · have h := hActual.2.2.2.symm
    change actual.outputTape.Equivalent finish.outputTape at h
    rw [hRestoredOutput] at h
    have hCombined :
        ((BinaryComparison.compare Ordering.eq (first.zip modulus) == Ordering.lt) && secondStatus) =
          decide (Binary.value first < Binary.value modulus ∧ Binary.value second < Binary.value modulus) := by
      change (firstStatus && secondStatus) = _
      simp [hFirstStatus, hSecondStatus]
    simpa only [hCombined] using h

/-- The status-only API is the projection of the stronger physical layout
result. Both numerical delimiters are restored on the same actual tape. -/
theorem runs_matching_decisions (n width : Nat)
    (modulus suffix first second tail : List Bool)
    (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputTape.left.getD 0 none =
        some (decide (Binary.value first < Binary.value modulus ∧
          Binary.value second < Binary.value modulus)) := by
  obtain ⟨target, used, run, hHalt, hStatus, _, _⟩ := runs_matching_layout n width
    modulus suffix first second tail hModulus hInstance hFirst hSecond
  exact ⟨target, used, run, hHalt, hStatus⟩

/-- Malformed and prematurely terminated inputs also stop. The stopping
proof uses actual tape storage after the preceding subroutine. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ := ChooseTwoRanges.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseTwoRanges.program
      (ChooseRangeStatusGate.program.asSubroutine gateEntry finalPc ++ [.halt])
      gateEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt gateEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseRangeStatusGate.runs_any after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseTwoRanges.program.asSubroutine 0 gateEntry)
      ChooseRangeStatusGate.program [.halt] finalPc (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt gateEntry)
      (finish.resumeAt finalPc) returned₂ := by
    simpa [second_layout, gateEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc,
      ChooseRangeStatusGate.entry] using embedded₂
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
  unfold budget
  exact ((PolynomiallyBounded.const 7).mul
    ((PolynomiallyBounded.id.add ChooseTwoRanges.budget_polynomial).add
      (PolynomiallyBounded.const 10))).add (PolynomiallyBounded.const 3)

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomial, haltsWithin⟩

end Machine.ChooseRangeValidation
