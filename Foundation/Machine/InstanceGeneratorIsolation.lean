import Foundation.Machine.InstanceGeneratorSkip
import Foundation.Machine.BitstringRewind
import Foundation.Machine.BitstringErasure
import Foundation.Machine.ContextualDelimiter

namespace Machine.InstanceGeneratorIsolation

private def mark : Program := [.moveLeft .input, .erase .input, .moveRight .input]
private def eraseEntry : Nat := mark.length + InstanceGeneratorSkip.program.length + 1
private def rewindEntry : Nat := eraseEntry + 1
private def clearEntry : Nat := rewindEntry + rewindBitstring.length + 1
private def finalPc : Nat := clearEntry + eraseOutputBlock.length + 1
private def beforeRewind : Program :=
  mark ++ InstanceGeneratorSkip.program.asSubroutine mark.length eraseEntry ++ [.erase .input]
private def beforeClear : Program := beforeRewind ++ rewindBitstring.asSubroutine rewindEntry clearEntry

/-- On the fallback path, isolate the stored instance generator by native
blank writes and a width-counted scan, rewind it, and clear the arithmetic
workspace. Only this working copy is modified. This code neither decodes
nor installs a generator value by a meta-level operation. -/
def program : Program :=
  beforeClear ++ eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]

private theorem skip_layout : program =
    Program.withSubroutine mark InstanceGeneratorSkip.program
      ([.erase .input] ++ rewindBitstring.asSubroutine rewindEntry clearEntry ++
        eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) eraseEntry := by
  simp [program, beforeClear, beforeRewind, Program.withSubroutine, List.append_assoc]

private theorem rewind_layout : program =
    Program.withSubroutine beforeRewind rewindBitstring
      (eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) clearEntry := by
  simp [program, beforeClear, beforeRewind, Program.withSubroutine, rewindEntry, eraseEntry,
    Program.asSubroutine_length, List.append_assoc, Nat.add_assoc]

private theorem clear_layout : program =
    Program.withSubroutine beforeClear eraseOutputBlock [.halt] finalPc := by
  simp [program, beforeClear, beforeRewind, Program.withSubroutine, clearEntry, rewindEntry,
    eraseEntry, Program.asSubroutine_length, List.append_assoc, Nat.add_assoc]
  congr 1 <;> omega

private theorem mark_run (input output : Tape) :
    RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 3, inputTape := (input.moveLeft.write none).moveRight, outputTape := output } : Configuration) 3 := by
  let moved : Configuration := { pc := 1, inputTape := input.moveLeft, outputTape := output }
  let erased : Configuration := { pc := 2, inputTape := input.moveLeft.write none, outputTape := output }
  have h₁ : Step program ({ inputTape := input, outputTape := output } : Configuration) moved := by
    simp [Step, successors, next, program, beforeClear, beforeRewind, mark, moved,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  have h₂ : Step program moved erased := by
    simp [Step, successors, next, program, beforeClear, beforeRewind, mark, moved, erased,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  have h₃ : Step program erased
      ({ pc := 3, inputTape := (input.moveLeft.write none).moveRight, outputTape := output } : Configuration) := by
    simp [Step, successors, next, program, beforeClear, beforeRewind, mark, erased,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  exact (((RunsFor.zero _).succ h₁).succ h₂).succ h₃

private theorem erase_step (c : Configuration) (hPc : c.pc = eraseEntry)
    (hActive : c.halted = false) :
    Step program c { c with pc := rewindEntry, inputTape := c.inputTape.write none } := by
  have hLookup : program[eraseEntry]? = some (.erase .input) := by
    rw [skip_layout]
    have hIndex : eraseEntry = mark.length + InstanceGeneratorSkip.program.length + 1 + 0 := rfl
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next,
    Configuration.advance, Configuration.updateTape, rewindEntry]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    rw [clear_layout]
    have hIndex : finalPc = beforeClear.length + eraseOutputBlock.length + 1 + 0 := by
      simp [finalPc, beforeClear, beforeRewind, clearEntry, rewindEntry, eraseEntry,
        mark, Program.asSubroutine_length, Nat.add_assoc]
      omega
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The generator bits are the original width-counted instance field.
They remain between two physical blanks, ready for native fallback output;
all former arithmetic columns are actually erased. The arbitrary reply may
be discarded on this branch, so its first cell supplies the end separator. -/
theorem runs_generator (firstBits exponent modulus generator reply : List Bool)
    (hFirst : firstBits.length = modulus.length)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (old : Option Bool) (before : List (Option Bool)) :
    let columns := BinaryColumnSlotFill.fullSlots firstBits exponent modulus
    let start : Configuration :=
      { inputTape := { Tape.ofBits (generator ++ reply) with left := old :: before },
        outputTape := { left := none :: columns.reverse.map some } }
    ∃ target used,
      RunsFor program start target used ∧ target.halted = true ∧
      (target.resumeAt 0).Equivalent
        (writeDelimitedContextStart (none :: before) [] (Tape.ofBits reply).right
          generator (columns.length + 1)) := by
  dsimp only
  let columns := BinaryColumnSlotFill.fullSlots firstBits exponent modulus
  let input : Tape := { Tape.ofBits (generator ++ reply) with left := old :: before }
  let output : Tape := { left := none :: columns.reverse.map some }
  let marked : Configuration :=
    { pc := 3, inputTape := { Tape.ofBits (generator ++ reply) with left := none :: before }, outputTape := output }
  have hMark : (input.moveLeft.write none).moveRight = marked.inputTape := by
    simp [input, marked, Tape.moveLeft, Tape.write, Tape.moveRight]
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration) marked 3 := by
    simpa only [hMark] using mark_run input output
  obtain ⟨skipped, u₂, _, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    InstanceGeneratorSkip.runs_generator firstBits exponent modulus generator reply
      hFirst hExponent hGenerator (none :: before)
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted
    mark InstanceGeneratorSkip.program
      ([.erase .input] ++ rewindBitstring.asSubroutine rewindEntry clearEntry ++
        eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) eraseEntry
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program marked (skipped.resumeAt eraseEntry) v₂ := by
    rw [skip_layout]
    exact embedded₂
  let canonical : Configuration :=
    { pc := eraseEntry,
      inputTape := { Tape.ofBits reply with left := generator.reverse.map some ++ none :: before },
      outputTape := { left := columns.reverse.map some } }
  have hLayout : canonical.Equivalent (skipped.resumeAt eraseEntry) :=
    ⟨rfl, rfl, hInput₂.symm, hOutput₂.symm⟩
  let erased : Configuration := { canonical with pc := rewindEntry, inputTape := canonical.inputTape.write none }
  have rErase : RunsFor program canonical erased 1 :=
    (RunsFor.zero _).succ (erase_step canonical rfl rfl)
  obtain ⟨actualErased, actualErase, hErased⟩ := rErase.exists_equivalent hLayout
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := before, right := generator.map some ++ none :: (Tape.ofBits reply).right } : Tape).moveRight,
      outputTape := canonical.outputTape, halted := true }
  have r₃ := rewindScratch_runs_from before generator none (Tape.ofBits reply).right canonical.outputTape
  have hStart : erased.resumeAt 0 =
      ({ inputTape := { left := generator.reverse.map some ++ none :: before,
                        right := (Tape.ofBits reply).right }, outputTape := canonical.outputTape } : Configuration) := rfl
  rw [← hStart] at r₃
  obtain ⟨v₃, _, embedded₃⟩ := r₃.withSubroutine_halted beforeRewind rewindBitstring
    (eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) clearEntry
    (Nat.zero_le _) rfl rfl
  have hEntry : (erased.resumeAt 0).rebasePc beforeRewind.length = erased := by
    simp [erased, beforeRewind, rewindEntry, eraseEntry, mark, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc, canonical, Nat.add_assoc]
    omega
  have r₃' : RunsFor program erased (rewound.resumeAt clearEntry) v₃ := by
    rw [rewind_layout]
    simpa only [hEntry] using embedded₃
  obtain ⟨actualRewound, actualRewind, hRewound⟩ := r₃'.exists_equivalent hErased
  have r₄ := eraseOutputBlock_runs rewound.inputTape [] columns []
  let cleared := eraseOutputBlockFinish rewound.inputTape [] columns []
  obtain ⟨v₄, _, embedded₄⟩ := r₄.withSubroutine_halted beforeClear eraseOutputBlock [.halt]
    finalPc (Nat.zero_le _) rfl rfl
  have hBlank : ({ left := columns.reverse.map some ++ [none] } : Tape).Equivalent canonical.outputTape := by
    refine ⟨rfl, ?_, fun _ => rfl⟩
    change ∀ i, (columns.reverse.map some ++ [none]).getD i none = (columns.reverse.map some).getD i none
    generalize columns.reverse.map some = cells
    induction cells with
    | nil => intro i; cases i <;> rfl
    | cons cell cells ih =>
        intro i
        cases i with
        | zero => rfl
        | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i
  have hClearCall : ((eraseOutputBlockStart rewound.inputTape [] columns []).rebasePc beforeClear.length).Equivalent
      actualRewound := by
    refine ⟨?_, ?_, ?_, hBlank.trans hRewound.2.2.2⟩
    · rw [← hRewound.1]
      change 0 + beforeClear.length = clearEntry
      simp [beforeClear, beforeRewind, clearEntry, rewindEntry, eraseEntry, mark,
        Program.asSubroutine_length, Configuration.rebasePc, Configuration.resumeAt,
        eraseOutputBlockStart, Nat.add_assoc]
      omega
    · exact hRewound.2.1
    · exact hRewound.2.2.1
  have r₄' : RunsFor program ((eraseOutputBlockStart rewound.inputTape [] columns []).rebasePc beforeClear.length)
      (cleared.resumeAt finalPc) v₄ := by rw [clear_layout]; exact embedded₄
  obtain ⟨actualCleared, actualClear, hCleared⟩ := r₄'.exists_equivalent hClearCall
  have hPc : actualCleared.pc = finalPc := by simpa [Configuration.resumeAt] using hCleared.1.symm
  have hActive : actualCleared.halted = false := hCleared.2.1.symm
  refine ⟨{ actualCleared with halted := true }, 3+v₂+1+v₃+v₄+1,
    ((((r₁.trans r₂).trans actualErase).trans actualRewind).trans actualClear).succ
      (final_step _ hPc hActive), rfl, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have hReady : rewound.inputTape =
        (writeDelimitedContextStart (none :: before) [] (Tape.ofBits reply).right
          generator (columns.length + 1)).inputTape := by
      cases generator <;> rfl
    rw [← hReady]
    exact hCleared.2.2.1.symm
  · have hReady : cleared.outputTape =
        (writeDelimitedContextStart (none :: before) [] (Tape.ofBits reply).right
          generator (columns.length + 1)).outputTape := by
      change ({ right := List.replicate (columns.reverse.length + 1) none ++ [] } : Tape) =
        { right := List.replicate (columns.length + 1) none }
      simp only [List.length_reverse, List.append_nil]
    rw [← hReady]
    exact hCleared.2.2.2.symm

/-- All finite physical tape layouts terminate, including malformed instance
fields. Correct interpretation of the isolated field needs the width premises
above; termination does not silently assume well-formed input. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 10000 * (input.cells + output.cells + 1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  let marked : Configuration :=
    { pc := 3, inputTape := (input.moveLeft.write none).moveRight, outputTape := output }
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration) marked 3 :=
    mark_run input output
  obtain ⟨skipped, u₂, hu₂, run₂, hHalt₂⟩ := InstanceGeneratorSkip.runs_any marked.inputTape marked.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted mark InstanceGeneratorSkip.program
    ([.erase .input] ++ rewindBitstring.asSubroutine rewindEntry clearEntry ++
      eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) eraseEntry
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program marked (skipped.resumeAt eraseEntry) v₂ := by
    rw [skip_layout]
    exact embedded₂
  let erased : Configuration :=
    { skipped.resumeAt eraseEntry with pc := rewindEntry, inputTape := skipped.inputTape.write none }
  have rErase : RunsFor program (skipped.resumeAt eraseEntry) erased 1 :=
    (RunsFor.zero _).succ (erase_step _ rfl rfl)
  obtain ⟨rewound, u₃, hu₃, run₃, hHalt₃, _⟩ :=
    rewindBitstring_terminates_from erased.inputTape erased.outputTape
  obtain ⟨v₃, hv₃, embedded₃⟩ := run₃.withSubroutine_halted beforeRewind rewindBitstring
    (eraseOutputBlock.asSubroutine clearEntry finalPc ++ [.halt]) clearEntry
    (Nat.zero_le _) rfl hHalt₃
  have hEntry : ({ inputTape := erased.inputTape, outputTape := erased.outputTape } : Configuration).rebasePc
      beforeRewind.length = erased := by
    simp [erased, beforeRewind, rewindEntry, eraseEntry, mark, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc, Nat.add_assoc]
    omega
  have r₃ : RunsFor program erased (rewound.resumeAt clearEntry) v₃ := by
    rw [rewind_layout]
    simpa only [hEntry] using embedded₃
  obtain ⟨cleared, u₄, hu₄, run₄, hHalt₄, _, _⟩ :=
    eraseOutputBlock_terminates_from_anyTape rewound.inputTape rewound.outputTape
  obtain ⟨v₄, hv₄, embedded₄⟩ := run₄.withSubroutine_halted beforeClear eraseOutputBlock [.halt]
    finalPc (Nat.zero_le _) rfl hHalt₄
  have hEntry₄ : ({ inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration).rebasePc
      beforeClear.length = rewound.resumeAt clearEntry := by
    simp [beforeClear, beforeRewind, clearEntry, rewindEntry, eraseEntry, mark,
      Program.asSubroutine_length, Configuration.resumeAt, Configuration.rebasePc, Nat.add_assoc]
    omega
  have r₄ : RunsFor program (rewound.resumeAt clearEntry) (cleared.resumeAt finalPc) v₄ := by
    rw [clear_layout]
    simpa only [hEntry₄] using embedded₄
  refine ⟨{ cleared.resumeAt finalPc with halted := true }, 3+v₂+1+v₃+v₄+1, ?_,
    ((((r₁.trans r₂).trans rErase).trans r₃).trans r₄).succ
      (final_step _ rfl rfl), rfl⟩
  have hs₁ := GuardedCompiler.sourceStorage_le_of_run r₁
  have hs₂ := GuardedCompiler.sourceStorage_le_of_run run₂
  have hsErase := GuardedCompiler.sourceStorage_le_of_run rErase
  have hs₃ := GuardedCompiler.sourceStorage_le_of_run run₃
  have hLeft₃ : erased.inputTape.left.length ≤ erased.inputTape.cells := by simp only [Tape.cells]; omega
  have hLeft₄ : rewound.outputTape.left.length ≤ rewound.outputTape.cells := by simp only [Tape.cells]; omega
  simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hs₁ hs₂ hsErase hs₃
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (30000 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hCells : (Tape.ofBits raw).cells ≤ raw.length + 1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 30000 * (m+1), (PolynomiallyBounded.const 30000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.InstanceGeneratorIsolation
