import Foundation.Machine.BinaryProductPadded

namespace Machine.BinaryProductExternalWidth

private def firstReturn (core : Program) : Nat := core.length + 1
private def pre (core : Program) : Program := core.asSubroutine 0 (firstReturn core)
private def finalReturn (core : Program) : Nat :=
  firstReturn core + BinaryWorkspaceStrip.program.length + 1

/-- Extend the raw input by a high zero column, compute the product on the
same tapes, then erase the extra output bit with three native instructions. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine (pre core) BinaryWorkspaceStrip.program [.halt]
    (finalReturn core)

def program : Program := withCore BinaryProductPadded.program

private theorem pre_length (core : Program) : (pre core).length = firstReturn core := by
  simp [pre, firstReturn]

private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] core
      (BinaryWorkspaceStrip.program.asSubroutine (firstReturn core) (finalReturn core) ++ [.halt])
      (firstReturn core) := by
  simp [withCore, pre, firstReturn, Program.withSubroutine,
    Program.asSubroutine_length]

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp only [program, withCore, Program.withSubroutine, pre,
    List.mem_append, not_or]
  exact ⟨⟨Program.asSubroutine_no_randomBit _ BinaryProductPadded.no_randomBit _ _ tape,
    Program.asSubroutine_no_randomBit _ BinaryWorkspaceStrip.no_randomBit _ _ tape⟩,
    by simp⟩

def budget (length : Nat) : Nat := BinaryProductPadded.budget length + 4

private theorem finalStep (core : Program) (actual : Configuration)
    (hpc : actual.pc = finalReturn core) (ha : actual.halted = false) :
    Step (withCore core) actual { actual with halted := true } := by
  have lookup : (withCore core)[finalReturn core]? = some .halt := by
    change (Program.withSubroutine (pre core) BinaryWorkspaceStrip.program [.halt]
      (finalReturn core))[finalReturn core]? = some .halt
    have hOffset : finalReturn core =
        (pre core).length + BinaryWorkspaceStrip.program.length + 1 + 0 := by
      simp [finalReturn, pre_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hpc, ha, lookup, Instruction.next]

private theorem rebase_start (base : Nat) (target : Configuration) :
    (({ inputTape := target.inputTape,
        outputTape := target.outputTape } : Configuration).rebasePc base) =
      target.resumeAt base := by
  simp [Configuration.rebasePc, Configuration.resumeAt]

/-- All finite raw inputs halt. The output layout records the actual strip
step, so correctness does not silently discard a high bit in Lean. -/
theorem runs (bits : List Bool) :
    ∃ paddedOutput target used blanks,
      used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) target used ∧
      target.halted = true ∧
      target.outputTape.Equivalent
        (({ left := paddedOutput.reverse.map some ++ [none],
             right := List.replicate blanks none } : Tape).moveLeft.write none) ∧
      evalWithin BinaryProductProgram.program (bits ++ [false, false, false])
        (BinaryProductProgram.budget (bits.length + 3)) =
        PMF.pure (some paddedOutput) := by
  obtain ⟨output, paddedTarget, u1, blanks, hu1, run1, hHalt1,
    hOutput1, hLayout1, hCoreEval⟩ := BinaryProductPadded.runs bits
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] BinaryProductPadded.program
    (BinaryWorkspaceStrip.program.asSubroutine
      (firstReturn BinaryProductPadded.program) (finalReturn BinaryProductPadded.program) ++ [.halt])
    (firstReturn BinaryProductPadded.program) (Nat.zero_le _) rfl hHalt1
  have rFirst : RunsFor program (Configuration.initial bits)
      (paddedTarget.resumeAt (firstReturn BinaryProductPadded.program)) v1 := by
    change RunsFor (withCore BinaryProductPadded.program) _ _ v1
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  let stripped : Configuration :=
    { pc := 2, inputTape := paddedTarget.inputTape,
      outputTape := paddedTarget.outputTape.moveLeft.write none, halted := true }
  obtain ⟨v2, hv2, embedded2⟩ :=
    (BinaryWorkspaceStrip.runs_any paddedTarget.inputTape paddedTarget.outputTape).withSubroutine_halted
      (pre BinaryProductPadded.program) BinaryWorkspaceStrip.program [.halt]
      (finalReturn BinaryProductPadded.program)
      (Nat.zero_le _) rfl rfl
  have hStart :
      (({ inputTape := paddedTarget.inputTape,
          outputTape := paddedTarget.outputTape } : Configuration).rebasePc
        (pre BinaryProductPadded.program).length) =
      paddedTarget.resumeAt (firstReturn BinaryProductPadded.program) := by
    exact (rebase_start (pre BinaryProductPadded.program).length paddedTarget).trans
      (congrArg (paddedTarget.resumeAt) (pre_length BinaryProductPadded.program))
  rw [hStart] at embedded2
  have rSecond : RunsFor program (paddedTarget.resumeAt (firstReturn BinaryProductPadded.program))
      (stripped.resumeAt (finalReturn BinaryProductPadded.program)) v2 := by
    exact embedded2
  have hFinal : Step program (stripped.resumeAt (finalReturn BinaryProductPadded.program))
      { stripped.resumeAt (finalReturn BinaryProductPadded.program) with halted := true } :=
    finalStep BinaryProductPadded.program _ rfl rfl
  refine ⟨output, { stripped.resumeAt (finalReturn BinaryProductPadded.program) with halted := true },
    v1 + v2 + 1, blanks, ?_, (rFirst.trans rSecond).succ hFinal, rfl, ?_, hCoreEval⟩
  · change v1 + v2 + 1 ≤ BinaryProductPadded.budget bits.length + 4
    omega
  · exact hLayout1.moveLeft.write none

/-- Every raw input terminates with arbitrary caller data stored behind a
blank separator. The external-width strip is performed on the actual
output tape after the contextual padded product. -/
theorem runs_with_saved (bits : List Bool) (before : List (Option Bool)) :
    ∃ (paddedOutput : List Bool) (target : Configuration) (used blanks : Nat),
      used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration) target used ∧
      target.halted = true ∧
      target.outputTape.Equivalent
        (({ left := paddedOutput.reverse.map some ++ [none],
             right := List.replicate blanks none } : Tape).moveLeft.write none) := by
  obtain ⟨output, paddedTarget, u1, blanks, hu1, run1, hHalt1,
    hOutput1, hLayout1⟩ := BinaryProductPadded.runs_with_saved bits before
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] BinaryProductPadded.program
    (BinaryWorkspaceStrip.program.asSubroutine
      (firstReturn BinaryProductPadded.program) (finalReturn BinaryProductPadded.program) ++ [.halt])
    (firstReturn BinaryProductPadded.program) (Nat.zero_le _) rfl hHalt1
  have rFirst : RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration)
      (paddedTarget.resumeAt (firstReturn BinaryProductPadded.program)) v1 := by
    change RunsFor (withCore BinaryProductPadded.program) _ _ v1
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  let stripped : Configuration :=
    { pc := 2, inputTape := paddedTarget.inputTape,
      outputTape := paddedTarget.outputTape.moveLeft.write none, halted := true }
  obtain ⟨v2, hv2, embedded2⟩ :=
    (BinaryWorkspaceStrip.runs_any paddedTarget.inputTape paddedTarget.outputTape).withSubroutine_halted
      (pre BinaryProductPadded.program) BinaryWorkspaceStrip.program [.halt]
      (finalReturn BinaryProductPadded.program)
      (Nat.zero_le _) rfl rfl
  have hStart :
      (({ inputTape := paddedTarget.inputTape,
          outputTape := paddedTarget.outputTape } : Configuration).rebasePc
        (pre BinaryProductPadded.program).length) =
      paddedTarget.resumeAt (firstReturn BinaryProductPadded.program) := by
    exact (rebase_start (pre BinaryProductPadded.program).length paddedTarget).trans
      (congrArg (paddedTarget.resumeAt) (pre_length BinaryProductPadded.program))
  rw [hStart] at embedded2
  have rSecond : RunsFor program (paddedTarget.resumeAt (firstReturn BinaryProductPadded.program))
      (stripped.resumeAt (finalReturn BinaryProductPadded.program)) v2 := by
    exact embedded2
  have hFinal : Step program (stripped.resumeAt (finalReturn BinaryProductPadded.program))
      { stripped.resumeAt (finalReturn BinaryProductPadded.program) with halted := true } :=
    finalStep BinaryProductPadded.program _ rfl rfl
  refine ⟨output, { stripped.resumeAt (finalReturn BinaryProductPadded.program) with halted := true },
    v1 + v2 + 1, blanks, ?_, (rFirst.trans rSecond).succ hFinal, rfl, ?_⟩
  · change v1 + v2 + 1 ≤ BinaryProductPadded.budget bits.length + 4
    omega
  · exact hLayout1.moveLeft.write none

theorem haltsFrom_with_saved (bits : List Bool) (before : List (Option Bool)) :
    ∀ target, PaddedRunsFor program
      ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration)
      target (budget bits.length) → target.halted = true := by
  obtain ⟨_, target, used, _, hUsed, run, hHalt, _⟩ :=
    runs_with_saved bits before
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨_, target, used, _, hUsed, run, hHalt, _, _⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

/-- The last output bit is erased by native code. The resulting bitstring
has exactly the external width, even when the internal product used a
larger working width. -/
theorem eval_product (columns : List BinaryModularAddition.Column)
    (hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    let raw := BinaryModularAddition.interleave columns
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) *
          Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)))) := by
  dsimp only
  let raw := BinaryModularAddition.interleave columns
  let expected := Binary.encode columns.length
    (Binary.value (columns.map fun c => c.1.1) *
      Binary.value (columns.map fun c => c.1.2) %
      Binary.value (columns.map Prod.snd))
  obtain ⟨output, target, used, blanks, hUsed, run, hHalted,
    hLayout, hCoreEval⟩ := runs raw
  have hPadded : BinaryModularAddition.interleave
      (BinaryWorkspacePadding.pad columns) = raw ++ [false, false, false] := by
    simp [raw]
  have hCore := BinaryWorkspacePadding.eval_product_padded columns hOperand hModWidth
  rw [hPadded] at hCore
  have hLen : (raw ++ [false, false, false]).length = raw.length + 3 := by simp
  rw [hLen] at hCore
  have hExpected : output = expected ++ [false] := by
    have hEq : PMF.pure (some output) = PMF.pure (some (expected ++ [false])) :=
      hCoreEval.symm.trans hCore
    have hMember : some output ∈ (PMF.pure (some (expected ++ [false]))).support := by
      rw [← hEq]
      simp
    simpa using hMember
  have hOutput : target.outputBits = expected := by
    have hTape : target.outputTape.Equivalent
        (BinaryWorkspaceStrip.finish target.inputTape expected).outputTape := by
      rw [hExpected] at hLayout
      refine hLayout.trans ?_
      exact ((BinaryWorkspaceStrip.padded_output_equivalent expected blanks).moveLeft).write none
    exact hTape.bits.trans (BinaryWorkspaceStrip.finish_outputBits target.inputTape expected)
  have hAll := run.haltsFrom_of_no_randomBit hHalted no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalted, hOutput, expected]

/-- The canonical halted trace has the same output as `eval_product`.
This form is convenient when a surrounding program embeds the multiplier
as a subroutine and transfers its trace from equivalent physical tapes. -/
theorem runs_product (columns : List BinaryModularAddition.Column)
    (hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    let raw := BinaryModularAddition.interleave columns
    ∃ target used,
      used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) *
          Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)) := by
  dsimp only
  let raw := BinaryModularAddition.interleave columns
  obtain ⟨_, target, used, _, hUsed, run, hHalt, _, _⟩ := runs raw
  have hEval : evalWithin program raw (budget raw.length) =
      PMF.pure (some target.outputBits) := by
    unfold evalWithin
    have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
      (Nat.le_refl used)
    rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
      run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit,
      PMF.pure_map]
    simp [hHalt]
  have hCorrect := eval_product columns hOperand hModWidth
  have hOutput : target.outputBits = Binary.encode columns.length
      (Binary.value (columns.map fun c => c.1.1) *
        Binary.value (columns.map fun c => c.1.2) %
        Binary.value (columns.map Prod.snd)) := by
    have hMember : some target.outputBits ∈
        (PMF.pure (some (Binary.encode columns.length
          (Binary.value (columns.map fun c => c.1.1) *
            Binary.value (columns.map fun c => c.1.2) %
            Binary.value (columns.map Prod.snd))))).support := by
      rw [← hCorrect, hEval]
      simp
    simpa using hMember
  exact ⟨target, used, hUsed, run, hHalt, hOutput⟩

/-- A raw request formed from three equal-width binary numbers. Framed
protocol parsing is a separate native-code obligation. -/
def numberColumns (width modulus first second : Nat) :
    List BinaryModularAddition.Column :=
  ((Binary.encode width first).zip (Binary.encode width second)).zip
    (Binary.encode width modulus)

theorem numberColumns_components (width modulus first second : Nat) :
    (numberColumns width modulus first second).length = width ∧
    (numberColumns width modulus first second).map (fun c => c.1.1) =
      Binary.encode width first ∧
    (numberColumns width modulus first second).map (fun c => c.1.2) =
      Binary.encode width second ∧
    (numberColumns width modulus first second).map Prod.snd =
      Binary.encode width modulus := by
  let firstBits := Binary.encode width first
  let secondBits := Binary.encode width second
  let modulusBits := Binary.encode width modulus
  have hFirst : firstBits.length = width := Binary.encode_length _ _
  have hSecond : secondBits.length = width := Binary.encode_length _ _
  have hModulus : modulusBits.length = width := Binary.encode_length _ _
  have hPair : (firstBits.zip secondBits).length = width := by
    simp [hFirst, hSecond]
  have hOuter : (firstBits.zip secondBits).length ≤ modulusBits.length := by
    omega
  have hOuter' : modulusBits.length ≤ (firstBits.zip secondBits).length := by
    omega
  refine ⟨by simp [numberColumns], ?_, ?_, ?_⟩
  · calc
      (numberColumns width modulus first second).map (fun c => c.1.1) =
          (((firstBits.zip secondBits).zip modulusBits).map Prod.fst).map Prod.fst := by
            simp only [List.map_map]
            rfl
      _ = firstBits := by
        rw [List.map_fst_zip hOuter,
          List.map_fst_zip (by omega : firstBits.length ≤ secondBits.length)]
  · calc
      (numberColumns width modulus first second).map (fun c => c.1.2) =
          (((firstBits.zip secondBits).zip modulusBits).map Prod.fst).map Prod.snd := by
            simp only [List.map_map]
            rfl
      _ = secondBits := by
        rw [List.map_fst_zip hOuter,
          List.map_snd_zip (by omega : secondBits.length ≤ firstBits.length)]
  · change ((firstBits.zip secondBits).zip modulusBits).map Prod.snd = modulusBits
    exact List.map_snd_zip hOuter'

/-- The external-width native program computes a residue product on a raw
triple assembled from fixed-width operands and modulus. -/
theorem eval_numbers (width modulus first second : Nat)
    (hFirst : first < modulus) (hSecond : second < modulus)
    (hModulus : modulus < 2 ^ width) :
    let raw := BinaryModularAddition.interleave
      (numberColumns width modulus first second)
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode width (first * second % modulus))) := by
  dsimp only
  let columns := numberColumns width modulus first second
  obtain ⟨hLength, hA, hB, hP⟩ :=
    numberColumns_components width modulus first second
  have hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd) := by
    rw [hA, hP, Binary.value_encode (hFirst.trans hModulus),
      Binary.value_encode hModulus]
    exact hFirst
  have hWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length := by
    rw [hP, Binary.value_encode hModulus, hLength]
    exact hModulus
  have h := eval_product columns hOperand hWidth
  simpa only [hA, hB, hP, hLength, Binary.value_encode (hFirst.trans hModulus),
    Binary.value_encode (hSecond.trans hModulus), Binary.value_encode hModulus, columns] using h

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  change PolynomiallyBounded (fun n => BinaryProductPadded.budget n + 4)
  exact BinaryProductPadded.budget_polynomiallyBounded.add (PolynomiallyBounded.const 4)

end Machine.BinaryProductExternalWidth
