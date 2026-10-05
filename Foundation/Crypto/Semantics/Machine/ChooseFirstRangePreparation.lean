import Foundation.Crypto.Semantics.Machine.ChooseFirstFieldRewind

set_option maxRecDepth 4096

namespace Machine.ChooseFirstRangePreparation

private def rewindEntry : Nat := ChooseSecondRangeCheck.program.length + 1
private def finalPc : Nat := rewindEntry + ChooseFirstFieldRewind.program.length + 1

/-- One fixed finite instruction list runs the framed two-width prefix,
checks the second range, and rewinds both tapes for the first range test. -/
def program : Program :=
  ChooseSecondRangeCheck.program.asSubroutine 0 rewindEntry ++
    ChooseFirstFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseSecondRangeCheck.program
      (ChooseFirstFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseSecondRangeCheck.program.asSubroutine 0 rewindEntry)
      ChooseFirstFieldRewind.program [.halt] finalPc := by
  simp [program, Program.withSubroutine, rewindEntry,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  exact Step.resumeAt_halt c finalPc hLookup

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat :=
  9 * (length + ChooseSecondRangeCheck.budget length + 10) + 3

/-- For width-matching replies, the connected program leaves the first
candidate and the stored modulus under the two heads. The second range
decision remains on the input tape after the second candidate. -/
theorem runs_matching_layout (n width : Nat)
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
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit first ++
            DelimitedTapeComparison.marked second ++
              (BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt)
                :: tail) with
          left := some false :: before } ∧
      target.outputTape.Equivalent (Tape.ofBits instanceBits) := by
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
  let compared := DelimitedTapeComparison.done
    (BinaryComparison.compare Ordering.eq (second.zip modulus))
    ((DelimitedTapeComparison.marked second).reverse.map some ++ beforeSecond)
    (modulus.reverse.map some) tail suffix
  obtain ⟨after, used₁, firstRun, hAfterHalt, _, hAfterInput, hAfterOutput⟩ :=
    ChooseSecondRangeCheck.runs_second_range n width modulus suffix
      first second tail hModulus hInstance hFirst hSecond
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    firstRun.withSubroutine_halted [] ChooseSecondRangeCheck.program
      (ChooseFirstFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry (Nat.zero_le _) rfl hAfterHalt
  have firstEmbedded : RunsFor program (Configuration.initial raw)
      (after.resumeAt rewindEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨rewound, used₂, secondRun, hRewoundHalt,
    hRewoundInput, hRewoundOutput⟩ :=
    ChooseFirstFieldRewind.runs_from_compared width before
      first second modulus suffix tail hFirst hSecond hModulus
  have hEquivalent :
      ((ChooseFirstFieldRewind.entry compared.inputTape compared.outputTape).rebasePc
        rewindEntry).Equivalent (after.resumeAt rewindEntry) := by
    exact ⟨rfl, rfl, hAfterInput.symm, hAfterOutput.symm⟩
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    secondRun.withSubroutine_halted
      (ChooseSecondRangeCheck.program.asSubroutine 0 rewindEntry)
      ChooseFirstFieldRewind.program [.halt] finalPc
      (Nat.zero_le _) rfl hRewoundHalt
  have secondEmbedded : RunsFor program
      ((ChooseFirstFieldRewind.entry compared.inputTape compared.outputTape).rebasePc
        rewindEntry)
      (rewound.resumeAt finalPc) returned₂ := by
    simpa [second_layout, rewindEntry, Program.asSubroutine_length,
      Configuration.rebasePc, compared, beforeSecond, List.map_reverse]
      using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    secondEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalPc := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalPc]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstEmbedded.trans actualRun).succ hLast, rfl, ?_, ?_⟩
  · exact hActual.2.2.1.symm.trans hRewoundInput
  · exact hActual.2.2.2.symm.trans hRewoundOutput

/-- The same fixed code halts on every finite raw input. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseSecondRangeCheck.runs_any raw
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseSecondRangeCheck.program
      (ChooseFirstFieldRewind.program.asSubroutine rewindEntry finalPc ++ [.halt])
      rewindEntry (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt rewindEntry) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseFirstFieldRewind.runs_any after.inputTape after.outputTape
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseSecondRangeCheck.program.asSubroutine 0 rewindEntry)
      ChooseFirstFieldRewind.program [.halt] finalPc
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt rewindEntry)
      (finish.resumeAt finalPc) returned₂ := by
    simpa [second_layout, rewindEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc,
      ChooseFirstFieldRewind.entry] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_initial_run run₁
  have hCells : after.inputTape.cells + after.outputTape.cells ≤
      raw.length + 2 + used₁ := hStorage
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
  unfold budget
  exact ((PolynomiallyBounded.const 9).mul
    ((PolynomiallyBounded.id.add hSecond).add
      (PolynomiallyBounded.const 10))).add
        (PolynomiallyBounded.const 3)

end Machine.ChooseFirstRangePreparation
