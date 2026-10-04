import Foundation.Machine.ChooseTwoWidthsPrefix
import Foundation.Machine.ChooseSecondFieldRewind

namespace Machine.ChooseRangePreparation

private def rewindEntry : Nat := ChooseTwoWidthsPrefix.program.length + 1
private def finalPc : Nat := rewindEntry + ChooseSecondFieldRewind.program.length + 1

/-- Parse the framed choose response, check both element widths, then
physically rewind to the second element and the first instance field.
This prepares a range comparison but does not itself validate residues. -/
def program : Program :=
  ChooseTwoWidthsPrefix.program.asSubroutine 0 rewindEntry ++
    ChooseSecondFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseTwoWidthsPrefix.program
      (ChooseSecondFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseTwoWidthsPrefix.program.asSubroutine 0 rewindEntry)
      ChooseSecondFieldRewind.program [.halt] finalPc := by
  simp [program, Program.withSubroutine, rewindEntry,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat :=
  9 * (length + ChooseTwoWidthsPrefix.budget length + 10) + 3

/-- The same finite program leaves the two heads at the second delimited
element and at the first bit of the retained `p ++ q ++ g` instance code.
No tape is rebuilt between the width scan and the rewind. -/
theorem runs_matching_layout (n width : Nat)
    (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
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
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit second ++ tail) with
          left := beforeSecond } ∧
      target.outputTape.Equivalent (Tape.ofBits instanceBits) := by
  dsimp only
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
  let secondFinish := DelimitedTripleWidthCheck.finish
    beforeSecond [none] instanceBits second tail
  obtain ⟨prefixFinish, prefixUsed, prefixRun, hPrefixHalt,
    hPrefixInput, hPrefixOutput⟩ :=
    ChooseTwoWidthsPrefix.runs_matching_layout n width
      instanceBits first second tail hLength hFirst hSecond
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    prefixRun.withSubroutine_halted [] ChooseTwoWidthsPrefix.program
      (ChooseSecondFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry (Nat.zero_le _) rfl hPrefixHalt
  have firstRun : RunsFor program (Configuration.initial raw)
      (prefixFinish.resumeAt rewindEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨rewindFinish, rewindUsed, _hRewindUsed, rewindRun,
    hRewindHalt, hRewindInput, hRewindOutput⟩ :=
    ChooseSecondFieldRewind.runs_matching_tapes
      beforeSecond instanceBits second tail (by omega)
  let expected := ChooseSecondFieldRewind.entry
    secondFinish.inputTape secondFinish.outputTape
  have hEquivalent : (expected.rebasePc rewindEntry).Equivalent
      (prefixFinish.resumeAt rewindEntry) := by
    exact ⟨rfl, rfl, hPrefixInput.symm, hPrefixOutput.symm⟩
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    rewindRun.withSubroutine_halted
      (ChooseTwoWidthsPrefix.program.asSubroutine 0 rewindEntry)
      ChooseSecondFieldRewind.program [.halt] finalPc
      (Nat.zero_le _) rfl hRewindHalt
  have secondRun : RunsFor program (expected.rebasePc rewindEntry)
      (rewindFinish.resumeAt finalPc) returned₂ := by
    simpa [second_layout, rewindEntry, Program.asSubroutine_length,
      Configuration.rebasePc] using embedded₂
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
  · exact hActual.2.2.1.symm.trans hRewindInput
  · exact hActual.2.2.2.symm.trans hRewindOutput

/-- The connected parser and rewind halt for every finite raw input.
No valid frame or response tag is required for the stopping theorem. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseTwoWidthsPrefix.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseTwoWidthsPrefix.program
      (ChooseSecondFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt rewindEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseSecondFieldRewind.runs_any after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseTwoWidthsPrefix.program.asSubroutine 0 rewindEntry)
      ChooseSecondFieldRewind.program [.halt] finalPc
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt rewindEntry)
      (finish.resumeAt finalPc) returned₂ := by
    simpa [second_layout, rewindEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc,
      ChooseSecondFieldRewind.entry] using embedded₂
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
    dsimp only [budget, ChooseTwoWidthsPrefix.budget] at *
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
  have hPrefix : PolynomiallyBounded ChooseTwoWidthsPrefix.budget := by
    unfold ChooseTwoWidthsPrefix.budget
    exact ((PolynomiallyBounded.const 100000000000).mul
      ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
        (PolynomiallyBounded.const 100000000000)
  unfold budget
  exact ((PolynomiallyBounded.const 9).mul
    ((PolynomiallyBounded.id.add
      hPrefix).add
        (PolynomiallyBounded.const 10))).add
          (PolynomiallyBounded.const 3)

end Machine.ChooseRangePreparation
