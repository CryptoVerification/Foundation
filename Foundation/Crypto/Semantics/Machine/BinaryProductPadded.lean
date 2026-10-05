import Foundation.Crypto.Semantics.Machine.BinaryWorkspaceStrip
import Foundation.Crypto.Semantics.Machine.BinaryProductProgram

namespace Machine.BinaryProductPadded

private def firstReturn : Nat := BinaryWorkspacePreparation.program.length + 1
private def pre : Program := BinaryWorkspacePreparation.program.asSubroutine 0 firstReturn
private def finalReturn (core : Program) : Nat := firstReturn + core.length + 1

/-- The same physical input tape is extended, rewound, and then consumed by
the native modular product code. The result still contains its extra high
workspace bit; output stripping is a separate native step. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine pre core [.halt] (finalReturn core)

def program : Program := withCore BinaryProductProgram.program

private theorem pre_length : pre.length = firstReturn := by
  simp [pre, firstReturn]

private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] BinaryWorkspacePreparation.program
      (core.asSubroutine firstReturn (finalReturn core) ++ [.halt]) firstReturn := by
  simp [withCore, pre, firstReturn, Program.withSubroutine,
    Program.asSubroutine_length]

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp only [program, withCore, Program.withSubroutine, pre,
    List.mem_append, not_or]
  exact ⟨⟨Program.asSubroutine_no_randomBit _
    BinaryWorkspacePreparation.no_randomBit _ _ tape,
    Program.asSubroutine_no_randomBit _ BinaryProductProgram.no_randomBit _ _ tape⟩,
    by simp⟩

def budget (length : Nat) : Nat :=
  BinaryWorkspacePreparation.budget length + BinaryProductProgram.budget (length + 3) + 1

private theorem finalStep (core : Program) (actual : Configuration)
    (hpc : actual.pc = finalReturn core) (ha : actual.halted = false) :
    Step (withCore core) actual { actual with halted := true } := by
  have lookup : (withCore core)[finalReturn core]? = some .halt := by
    change (Program.withSubroutine pre core [.halt] (finalReturn core))[finalReturn core]? =
      some .halt
    have hOffset : finalReturn core = pre.length + core.length + 1 + 0 := by
      simp [finalReturn, pre_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hpc, ha, lookup, Instruction.next]

/-- All finite raw requests terminate, including truncated triples and
numerically invalid moduli. The native preprocessing cost and the product
cost are charged in the one final program. -/
theorem runs (bits : List Bool) :
    ∃ output target used blanks, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true ∧ target.outputBits = output ∧
      target.outputTape.Equivalent
        { left := output.reverse.map some ++ [none], right := List.replicate blanks none } ∧
      evalWithin BinaryProductProgram.program (bits ++ [false, false, false])
        (BinaryProductProgram.budget (bits.length + 3)) = PMF.pure (some output) := by
  let padded := bits ++ [false, false, false]
  obtain ⟨u1, hu1, r1⟩ := BinaryWorkspacePreparation.runs bits
  obtain ⟨v1, hv1, embedded1⟩ := r1.withSubroutine_halted
    [] BinaryWorkspacePreparation.program
    (BinaryProductProgram.program.asSubroutine firstReturn
      (finalReturn BinaryProductProgram.program) ++ [.halt]) firstReturn
    (by change 0 ≤ _; omega) rfl rfl
  have rFirst : RunsFor program (Configuration.initial bits)
      ((BinaryWorkspacePreparation.finish bits).resumeAt firstReturn) v1 := by
    simpa only [← first_layout, program, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  obtain ⟨output, canonical, u2, blanks, _, hu2, run2, hHalt2, hOutput2,
    hLayout2⟩ :=
    BinaryProductProgram.runs_with_layout padded
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    pre BinaryProductProgram.program [.halt] (finalReturn BinaryProductProgram.program)
    (by change 0 ≤ _; omega) rfl hHalt2
  have hJoin : ((Configuration.initial padded).rebasePc pre.length).Equivalent
      ((BinaryWorkspacePreparation.finish bits).resumeAt firstReturn) := by
    refine ⟨by simp [pre_length, Configuration.rebasePc, Configuration.resumeAt,
        Configuration.initial],
      rfl, ?_, Tape.Equivalent.refl _⟩
    simpa only [Configuration.rebasePc, Configuration.resumeAt,
      Configuration.initial, Configuration.inputTape] using
      (BinaryWorkspacePreparation.finish_input bits).symm
  obtain ⟨actual, r2, e2⟩ := embedded2.exists_equivalent hJoin
  have rSecond : RunsFor program
      ((BinaryWorkspacePreparation.finish bits).resumeAt firstReturn) actual v2 := by
    exact r2
  have hFinal : Step program actual { actual with halted := true } :=
    finalStep BinaryProductProgram.program actual e2.1.symm e2.2.1.symm
  have hPadded : padded.length = bits.length + 3 := by simp [padded]
  have hCoreAll := run2.haltsFrom_of_no_randomBit hHalt2
    BinaryProductProgram.no_randomBit (Nat.le_refl u2)
  have hCoreEval : evalWithin BinaryProductProgram.program padded
      (BinaryProductProgram.budget (bits.length + 3)) = PMF.pure (some output) := by
    unfold evalWithin
    rw [← hPadded, evalConfigWithin_eq_of_le _ _ _ _ hu2 hCoreAll,
      run2.evalConfigWithin_eq_pure_of_no_randomBit BinaryProductProgram.no_randomBit]
    simp [PMF.pure_map, hHalt2, hOutput2]
  refine ⟨output, { actual with halted := true }, v1 + v2 + 1, blanks, ?_,
    (rFirst.trans rSecond).succ hFinal, rfl, ?_, ?_, ?_⟩
  · change v1 + v2 + 1 ≤ BinaryWorkspacePreparation.budget bits.length +
      BinaryProductProgram.budget (bits.length + 3) + 1
    rw [hPadded] at hu2
    omega
  · have same := e2.2.2.2.bits.symm
    change actual.outputBits = canonical.outputBits at same
    exact same.trans hOutput2
  · have same := e2.2.2.2.symm
    change actual.outputTape.Equivalent canonical.outputTape at same
    exact same.trans hLayout2
  · simpa only [padded] using hCoreEval

/-- The native padded product retains caller cells behind a blank input
separator while it performs the same bounded arithmetic trace. -/
theorem runs_with_saved (bits : List Bool) (before : List (Option Bool)) :
    ∃ output target used blanks, used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration)
        target used ∧
      target.halted = true ∧ target.outputBits = output ∧
      target.outputTape.Equivalent
        { left := output.reverse.map some ++ [none],
          right := List.replicate blanks none } := by
  let padded := bits ++ [false, false, false]
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    BinaryWorkspacePreparation.runs_with_saved bits before
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] BinaryWorkspacePreparation.program
    (BinaryProductProgram.program.asSubroutine firstReturn
      (finalReturn BinaryProductProgram.program) ++ [.halt]) firstReturn
    (by change 0 ≤ _; omega) rfl hHalt1
  have rFirst : RunsFor program
      ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration)
      (prepared.resumeAt firstReturn) v1 := by
    simpa only [← first_layout, program, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  obtain ⟨output, canonical, u2, blanks, _, hu2, run2, hHalt2,
    hOutput2, hLayout2⟩ := BinaryProductProgram.runs_with_saved padded before
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    pre BinaryProductProgram.program [.halt] (finalReturn BinaryProductProgram.program)
    (by change 0 ≤ _; omega) rfl hHalt2
  have hJoin : (({ inputTape :=
        { Tape.ofBits padded with left := none :: before } } : Configuration).rebasePc
        pre.length).Equivalent (prepared.resumeAt firstReturn) := by
    refine ⟨by simp [pre_length, Configuration.rebasePc, Configuration.resumeAt],
      rfl, ?_, ?_⟩
    simpa only [Configuration.rebasePc, Configuration.resumeAt,
      Configuration.inputTape, hInput1] using
      (BinaryWorkspacePreparation.saved_input_equivalent bits before).symm
    simpa [Configuration.rebasePc, Configuration.resumeAt, hOutput1] using
      (Tape.Equivalent.refl ({} : Tape))
  obtain ⟨actual, r2, e2⟩ := embedded2.exists_equivalent hJoin
  have hFinal : Step program actual { actual with halted := true } :=
    finalStep BinaryProductProgram.program actual e2.1.symm e2.2.1.symm
  have hPadded : padded.length = bits.length + 3 := by simp [padded]
  refine ⟨output, { actual with halted := true }, v1 + v2 + 1, blanks, ?_,
    (rFirst.trans r2).succ hFinal, rfl, ?_, ?_⟩
  · change v1 + v2 + 1 ≤ BinaryWorkspacePreparation.budget bits.length +
      BinaryProductProgram.budget (bits.length + 3) + 1
    rw [hPadded] at hu2
    omega
  · exact e2.2.2.2.bits.symm.trans hOutput2
  · exact e2.2.2.2.symm.trans hLayout2

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨_, target, used, _, hUsed, run, hHalt, _, _, _⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

/-- Numerical correctness of the single padded native product program.
The three high zero bits are written by the preparation code, then the
ordinary product evaluator runs on the same tape. The high output bit is
still present and must be erased by a subsequent native strip invocation. -/
theorem eval_product_padded (columns : List BinaryModularAddition.Column)
    (hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    let raw := BinaryModularAddition.interleave columns
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) *
          Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)) ++ [false])) := by
  dsimp only
  let raw := BinaryModularAddition.interleave columns
  let expected := Binary.encode columns.length
    (Binary.value (columns.map fun c => c.1.1) *
      Binary.value (columns.map fun c => c.1.2) %
      Binary.value (columns.map Prod.snd)) ++ [false]
  obtain ⟨output, target, used, _, hUsed, run, hHalted, hOutput, _, hCoreEval⟩ := runs raw
  have hPadded : BinaryModularAddition.interleave
      (BinaryWorkspacePadding.pad columns) = raw ++ [false, false, false] := by
    simp [raw]
  have hCore := BinaryWorkspacePadding.eval_product_padded columns hOperand hModWidth
  rw [hPadded] at hCore
  have hLen : (raw ++ [false, false, false]).length = raw.length + 3 := by simp
  rw [hLen] at hCore
  have hExpected : output = expected := by
    have hEq : PMF.pure (some output) = PMF.pure (some expected) :=
      hCoreEval.symm.trans hCore
    have hMember : some output ∈ (PMF.pure (some expected)).support := by
      rw [← hEq]
      simp
    simpa using hMember
  have hAll := run.haltsFrom_of_no_randomBit hHalted no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalted, hOutput, hExpected, expected]

theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  exact ((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id |>.add
      (PolynomiallyBounded.const 19)).add
    ((PolynomiallyBounded.const 1000000).mul
      ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 4)).pow 4)) |>.add
      (PolynomiallyBounded.const 1)

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

end Machine.BinaryProductPadded
