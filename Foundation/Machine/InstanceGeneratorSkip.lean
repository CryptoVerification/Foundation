import Foundation.Machine.OneFieldColumnSkip
import Foundation.Machine.OutputColumnRewind
import Foundation.Machine.GuardedTrace

namespace Machine.InstanceGeneratorSkip

private def firstReturn : Nat := OutputColumnRewind.secondBoundaryToFirst.length + 1
private def finalReturn : Nat := firstReturn + OneFieldColumnSkip.program.length + 1
private def first : Program := OutputColumnRewind.secondBoundaryToFirst.asSubroutine 0 firstReturn
private def second : Program := OneFieldColumnSkip.program.asSubroutine firstReturn finalReturn

/-- After the exponent copy, rewind the populated arithmetic columns and
use their width to skip the instance generator. This consumes one actual
input cell per column and never decodes the generator as a free operation. -/
def program : Program := first ++ second ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] OutputColumnRewind.secondBoundaryToFirst
      (second ++ [.halt]) firstReturn := by
  simp [program, first, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine first OneFieldColumnSkip.program [.halt] finalReturn := by
  simp [program, second, first, firstReturn, Program.asSubroutine_length,
    Program.withSubroutine]

private theorem final_step (c : Configuration) (hPc : c.pc = finalReturn)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [second_layout]
    have hIndex : finalReturn = first.length + OneFieldColumnSkip.program.length + 1 + 0 := by
      simp [finalReturn, first, firstReturn, Program.asSubroutine_length]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The response frame and every previously consumed byte survive the
physical generator scan. The output head ends at the arithmetic block's
right boundary, ready for the existing output rewind. -/
theorem runs_generator (firstBits exponent modulus generator reply : List Bool)
    (hFirst : firstBits.length = modulus.length)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (before : List (Option Bool)) :
    let columns := BinaryColumnSlotFill.fullSlots firstBits exponent modulus
    let start : Configuration :=
      { inputTape := { Tape.ofBits (generator ++ reply) with left := before },
        outputTape := { left := none :: columns.reverse.map some } }
    ∃ target used, used ≤ 2 * columns.length + 6 * modulus.length + 10 ∧
      RunsFor program start target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits reply with left := generator.reverse.map some ++ before } ∧
      target.outputTape.Equivalent { left := columns.reverse.map some } := by
  dsimp only
  let columns := BinaryColumnSlotFill.fullSlots firstBits exponent modulus
  let input : Tape := { Tape.ofBits (generator ++ reply) with left := before }
  obtain ⟨rewound, u₁, hu₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs columns input
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] OutputColumnRewind.secondBoundaryToFirst (second ++ [.halt]) firstReturn
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program
      ({ inputTape := input, outputTape := { left := none :: columns.reverse.map some } } : Configuration)
      (rewound.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  let canonical : Configuration := { inputTape := input, outputTape := Tape.ofBits columns }
  let finished : Configuration :=
    { pc := 6, inputTape := { Tape.ofBits reply with left := generator.reverse.map some ++ before },
      outputTape := { left := columns.reverse.map some }, halted := true }
  have hEval : evalConfigWithin OneFieldColumnSkip.program canonical
      (6 * modulus.length + 2) = PMF.pure finished := by
    have h := OneFieldColumnSkip.eval_generator firstBits exponent modulus generator reply
      hFirst hExponent hGenerator before []
    have hEmpty : { Tape.ofBits columns with left := [] } = Tape.ofBits columns := by
      cases columns <;> rfl
    change evalConfigWithin OneFieldColumnSkip.program
      { inputTape := input, outputTape := { Tape.ofBits columns with left := [] } }
      (6 * modulus.length + 2) = PMF.pure
      { pc := 6, inputTape := { Tape.ofBits reply with left := generator.reverse.map some ++ before },
        outputTape := { left := columns.reverse.map some ++ [] }, halted := true } at h
    simpa only [hEmpty, List.append_nil] using h
  have hNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ OneFieldColumnSkip.program := by
    cases tape <;> decide
  have hSupport : finished ∈ (evalConfigWithin OneFieldColumnSkip.program canonical
      (6 * modulus.length + 2)).support := by rw [hEval]; simp
  obtain ⟨u₂, hu₂, run₂⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first OneFieldColumnSkip.program [.halt] finalReturn (Nat.zero_le _) rfl rfl
  have hCall : (canonical.rebasePc first.length).Equivalent (rewound.resumeAt firstReturn) := by
    refine ⟨?_, rfl, ?_, hOutput₁.symm⟩
    · simp [canonical, first, firstReturn, Program.asSubroutine_length,
        Configuration.rebasePc, Configuration.resumeAt]
    · exact hInput₁ ▸ Tape.Equivalent.refl _
  have r₂ : RunsFor program (canonical.rebasePc first.length)
      (finished.resumeAt finalReturn) v₂ := by rw [second_layout]; exact embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalReturn := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁ + v₂ + 1, ?_,
    (r₁.trans actualRun₂).succ (final_step actual hPc hActive), rfl,
    hActual.2.2.1.symm, hActual.2.2.2.symm⟩
  dsimp only [columns] at hu₁
  omega

/-- Arbitrary finite physical tapes also stop. The rewind's left segment
and the skip's right segment bound the two scans independently. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 100 * (input.cells + output.cells + 1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  obtain ⟨rewound, u₁, hu₁, run₁, hHalt₁, hInput₁⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs_any input output
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] OutputColumnRewind.secondBoundaryToFirst (second ++ [.halt]) firstReturn
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (rewound.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨skipped, u₂, hu₂, run₂, hHalt₂⟩ :=
    OneFieldColumnSkip.runs_any rewound.inputTape rewound.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first OneFieldColumnSkip.program [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (rewound.resumeAt firstReturn) (skipped.resumeAt finalReturn) v₂ := by
    rw [second_layout]
    simpa [first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run₁
  have hCells : rewound.outputTape.right.length ≤ rewound.outputTape.cells := by
    simp [Tape.cells]
  have hPc : (skipped.resumeAt finalReturn).pc = finalReturn := rfl
  have hActive : (skipped.resumeAt finalReturn).halted = false := rfl
  refine ⟨{ skipped.resumeAt finalReturn with halted := true }, v₁ + v₂ + 1,
    ?_, (r₁.trans r₂).succ (final_step _ hPc hActive), rfl⟩
  simp only [GuardedCompiler.sourceStorage] at hStorage
  have hLeft : output.left.length ≤ output.cells := by simp only [Tape.cells]; omega
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (300 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hCells : (Tape.ofBits raw).cells ≤ raw.length + 1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 300 * (m + 1), (PolynomiallyBounded.const 300).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.InstanceGeneratorSkip
