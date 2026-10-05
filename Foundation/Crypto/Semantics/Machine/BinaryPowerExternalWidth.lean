import Foundation.Crypto.Semantics.Machine.BinaryPowerPadded
import Foundation.Crypto.Semantics.Machine.BinaryProductExternalWidth

namespace Machine.BinaryPowerExternalWidth

private def firstReturn (core : Program) : Nat := core.length + 1
private def pre (core : Program) : Program := core.asSubroutine 0 (firstReturn core)
private def finalReturn (core : Program) : Nat :=
  firstReturn core + BinaryWorkspaceStrip.program.length + 1

/-- Extend the raw input by a high zero column, compute the power on the
same tapes, then erase the extra output bit with three native instructions. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine (pre core) BinaryWorkspaceStrip.program [.halt]
    (finalReturn core)

def program : Program := withCore BinaryPowerPadded.program

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
  exact ⟨⟨Program.asSubroutine_no_randomBit _ BinaryPowerPadded.no_randomBit _ _ tape,
    Program.asSubroutine_no_randomBit _ BinaryWorkspaceStrip.no_randomBit _ _ tape⟩,
    by simp⟩

def budget (length : Nat) : Nat := BinaryPowerPadded.budget length + 4

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
      evalWithin BinaryPowerProgram.program (bits ++ [false, false, false])
        (BinaryPowerProgram.budget (bits.length + 3)) =
        PMF.pure (some paddedOutput) := by
  obtain ⟨output, paddedTarget, u1, blanks, hu1, run1, hHalt1,
    hOutput1, hLayout1, hCoreEval⟩ := BinaryPowerPadded.runs bits
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] BinaryPowerPadded.program
    (BinaryWorkspaceStrip.program.asSubroutine
      (firstReturn BinaryPowerPadded.program) (finalReturn BinaryPowerPadded.program) ++ [.halt])
    (firstReturn BinaryPowerPadded.program) (Nat.zero_le _) rfl hHalt1
  have rFirst : RunsFor program (Configuration.initial bits)
      (paddedTarget.resumeAt (firstReturn BinaryPowerPadded.program)) v1 := by
    change RunsFor (withCore BinaryPowerPadded.program) _ _ v1
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  let stripped : Configuration :=
    { pc := 2, inputTape := paddedTarget.inputTape,
      outputTape := paddedTarget.outputTape.moveLeft.write none, halted := true }
  obtain ⟨v2, hv2, embedded2⟩ :=
    (BinaryWorkspaceStrip.runs_any paddedTarget.inputTape paddedTarget.outputTape).withSubroutine_halted
      (pre BinaryPowerPadded.program) BinaryWorkspaceStrip.program [.halt]
      (finalReturn BinaryPowerPadded.program)
      (Nat.zero_le _) rfl rfl
  have hStart :
      (({ inputTape := paddedTarget.inputTape,
          outputTape := paddedTarget.outputTape } : Configuration).rebasePc
        (pre BinaryPowerPadded.program).length) =
      paddedTarget.resumeAt (firstReturn BinaryPowerPadded.program) := by
    exact (rebase_start (pre BinaryPowerPadded.program).length paddedTarget).trans
      (congrArg (paddedTarget.resumeAt) (pre_length BinaryPowerPadded.program))
  rw [hStart] at embedded2
  have rSecond : RunsFor program (paddedTarget.resumeAt (firstReturn BinaryPowerPadded.program))
      (stripped.resumeAt (finalReturn BinaryPowerPadded.program)) v2 := by
    exact embedded2
  have hFinal : Step program (stripped.resumeAt (finalReturn BinaryPowerPadded.program))
      { stripped.resumeAt (finalReturn BinaryPowerPadded.program) with halted := true } :=
    finalStep BinaryPowerPadded.program _ rfl rfl
  refine ⟨output, { stripped.resumeAt (finalReturn BinaryPowerPadded.program) with halted := true },
    v1 + v2 + 1, blanks, ?_, (rFirst.trans rSecond).succ hFinal, rfl, ?_, hCoreEval⟩
  · change v1 + v2 + 1 ≤ BinaryPowerPadded.budget bits.length + 4
    omega
  · exact hLayout1.moveLeft.write none

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨_, target, used, _, hUsed, run, hHalt, _, _⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

/-- The last output bit is erased by native code. The resulting bitstring
has exactly the external width, even when the internal power used a
larger working width. -/
theorem eval_power (columns : List BinaryModularAddition.Column)
    (hNonempty : columns ≠ [])
    (hOne : 1 < Binary.value (columns.map Prod.snd))
    (hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    let raw := BinaryModularAddition.interleave columns
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) ^
          Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)))) := by
  dsimp only
  let raw := BinaryModularAddition.interleave columns
  let expected := Binary.encode columns.length
    (Binary.value (columns.map fun c => c.1.1) ^
      Binary.value (columns.map fun c => c.1.2) %
      Binary.value (columns.map Prod.snd))
  obtain ⟨output, target, used, blanks, hUsed, run, hHalted,
    hLayout, hCoreEval⟩ := runs raw
  have hPadded : BinaryModularAddition.interleave
      (BinaryWorkspacePadding.pad columns) = raw ++ [false, false, false] := by
    simp [raw]
  have hCore := BinaryWorkspacePadding.eval_power_padded columns hNonempty hOne hOperand hModWidth
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

/-- The enlarged native power code computes an encoded residue power on
an assembled raw triple. The request-frame adapter remains separate. -/
theorem eval_numbers (width modulus first exponent : Nat)
    (hOne : 1 < modulus) (hFirst : first < modulus)
    (hExponent : exponent < 2 ^ width)
    (hModulus : modulus < 2 ^ width) :
    let raw := BinaryModularAddition.interleave
      (BinaryProductExternalWidth.numberColumns width modulus first exponent)
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode width (first ^ exponent % modulus))) := by
  dsimp only
  let columns := BinaryProductExternalWidth.numberColumns width modulus first exponent
  obtain ⟨hLength, hA, hExponentBits, hP⟩ :=
    BinaryProductExternalWidth.numberColumns_components width modulus first exponent
  have hNonempty : columns ≠ [] := by
    intro hNil
    have hPositive : 0 < width := by
      by_contra h
      have hz : width = 0 := by omega
      simp [hz] at hModulus
      omega
    have hLen : columns.length = width := hLength
    rw [hNil] at hLen
    simp at hLen
    omega
  have hOneBits : 1 < Binary.value (columns.map Prod.snd) := by
    rw [hP, Binary.value_encode hModulus]
    exact hOne
  have hOperand : Binary.value (columns.map fun c => c.1.1) <
      Binary.value (columns.map Prod.snd) := by
    rw [hA, hP, Binary.value_encode (hFirst.trans hModulus),
      Binary.value_encode hModulus]
    exact hFirst
  have hWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length := by
    rw [hP, Binary.value_encode hModulus, hLength]
    exact hModulus
  have h := eval_power columns hNonempty hOneBits hOperand hWidth
  simpa only [hA, hExponentBits, hP, hLength,
    Binary.value_encode (hFirst.trans hModulus),
    Binary.value_encode hExponent, Binary.value_encode hModulus, columns] using h

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  change PolynomiallyBounded (fun n => BinaryPowerPadded.budget n + 4)
  exact BinaryPowerPadded.budget_polynomiallyBounded.add (PolynomiallyBounded.const 4)

end Machine.BinaryPowerExternalWidth
