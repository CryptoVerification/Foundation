import Foundation.Crypto.Semantics.Machine.DelimitedColumnSlotFill
import Foundation.Crypto.Semantics.Machine.GuardedOutput
import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine.ChooseCandidatePowerPreparation

private def seekEntry : Nat := DelimitedColumnSlotFill.program.length + 1
private def rewindEntry : Nat := seekEntry + GuardedCompiler.seekScratchInput.length + 1
private def finalPc : Nat := rewindEntry + OutputColumnRewind.toFirst.length + 1
private def beforeSeek : Program := DelimitedColumnSlotFill.program.asSubroutine 0 seekEntry
private def beforeRewind : Program := beforeSeek ++
  GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry

/-- Physically copy the delimited candidate into the first arithmetic track,
move the retained response to a saved prefix, and rewind the arithmetic input.
The next caller can invoke the opposite-tape power interpreter without loading
any newly constructed bitstring into a tape. -/
def program : Program := beforeRewind ++
  OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] DelimitedColumnSlotFill.program
      (GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry ++
        OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) seekEntry := by
  simp [program, beforeRewind, beforeSeek, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine beforeSeek GuardedCompiler.seekScratchInput
      (OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry := by
  simp [program, beforeRewind, beforeSeek, Program.withSubroutine,
    seekEntry, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine beforeRewind OutputColumnRewind.toFirst [.halt] finalPc := by
  simp [program, beforeRewind, beforeSeek, Program.withSubroutine,
    seekEntry, rewindEntry, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc) { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    rw [third_layout]
    have hIndex : finalPc = beforeRewind.length + OutputColumnRewind.toFirst.length + 1 + 0 := by
      simp [finalPc, beforeRewind, beforeSeek, seekEntry, rewindEntry,
        Program.asSubroutine_length, Nat.add_assoc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, Configuration.resumeAt, hLookup, Instruction.next]

/-- The original response, including its unexamined state bits, is retained
behind a real blank separator. The output head is at the prepared arithmetic
input. Tape equivalence only disregards outer blank padding created by rewind. -/
theorem runs_field (before : List (Option Bool))
    (old candidate exponent modulus tail : List Bool)
    (hOld : old.length = modulus.length)
    (hCandidate : candidate.length = modulus.length)
    (hExponent : exponent.length = modulus.length) :
    let slots := BinaryColumnSlotFill.fullSlots candidate exponent modulus
    let saved := none :: (false :: tail).reverse.map some ++
      (DelimitedTapeComparison.marked candidate).reverse.map some ++ before
    ∃ target used,
      used ≤ 10 * candidate.length + 2 + 3 * (false :: tail).length + 3 +
        2 * slots.length + 4 + 1 ∧
      RunsFor program
        (DelimitedColumnSlotFill.entry
          { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
          (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus))) target used ∧
      target.halted = true ∧
      target.inputTape = ({ left := saved } : Tape) ∧
      target.outputTape.Equivalent (Tape.ofBits slots) := by
  dsimp only
  let slots := BinaryColumnSlotFill.fullSlots candidate exponent modulus
  let copiedBefore := (DelimitedTapeComparison.marked candidate).reverse.map some ++ before
  let saved := none :: (false :: tail).reverse.map some ++ copiedBefore
  let copied := DelimitedColumnSlotFill.finish
    { Tape.ofBits (false :: tail) with left := copiedBefore }
    { left := slots.reverse.map some }
  have hCopy := DelimitedColumnSlotFill.eval_power_slots before [] old candidate
    exponent modulus tail hOld hCandidate hExponent
  have hCopyEval : evalConfigWithin DelimitedColumnSlotFill.program
      (DelimitedColumnSlotFill.entry
        { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
        (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (10 * candidate.length + 2) = PMF.pure copied := by
    have hEmpty (bits : List Bool) :
        ({ Tape.ofBits bits with left := [] } : Tape) = Tape.ofBits bits := by
      cases bits <;> rfl
    rw [hEmpty] at hCopy
    simpa [copied, slots, copiedBefore] using hCopy
  have hSupport : copied ∈ (evalConfigWithin DelimitedColumnSlotFill.program
      (DelimitedColumnSlotFill.entry
        { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
        (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (10 * candidate.length + 2)).support := by rw [hCopyEval]; simp
  obtain ⟨u, hu, copyRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  obtain ⟨u', hu', copyEmbedded⟩ := copyRun.withSubroutine_halted
    [] DelimitedColumnSlotFill.program
    (GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry ++
      OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) seekEntry
    (Nat.zero_le _) rfl rfl
  have r₁ : RunsFor program
      (DelimitedColumnSlotFill.entry
        { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
        (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (copied.resumeAt seekEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using copyEmbedded
  let sought := GuardedCompiler.seekScratchInputFinish copiedBefore (false :: tail)
    { left := slots.reverse.map some }
  have seekRun := GuardedCompiler.seekScratchInput_runs copiedBefore (false :: tail)
    ({ left := slots.reverse.map some } : Tape)
  change RunsFor GuardedCompiler.seekScratchInput (copied.resumeAt 0) sought _ at seekRun
  obtain ⟨v, hv, seekEmbedded⟩ := seekRun.withSubroutine_halted beforeSeek
    GuardedCompiler.seekScratchInput
    (OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry
    (by simp [Configuration.resumeAt]) rfl rfl
  have r₂ : RunsFor program (copied.resumeAt seekEntry) (sought.resumeAt rewindEntry) v := by
    simpa [second_layout, beforeSeek, seekEntry, Program.asSubroutine_length,
      copied, sought, GuardedCompiler.seekScratchInputStart,
      Configuration.resumeAt, Configuration.rebasePc, DelimitedColumnSlotFill.finish,
      copiedBefore, slots] using seekEmbedded
  let retained : Tape := { left := saved }
  obtain ⟨w, hw, rewindRun, hOutput⟩ := OutputColumnRewind.toFirst_runs slots retained
  let rewound := (rewindBitstringFinish slots retained).swapTapes
  obtain ⟨w', hw', rewindEmbedded⟩ := rewindRun.withSubroutine_halted beforeRewind
    OutputColumnRewind.toFirst [.halt] finalPc (Nat.zero_le _) rfl rfl
  have r₃ : RunsFor program (sought.resumeAt rewindEntry) (rewound.resumeAt finalPc) w' := by
    simpa [third_layout, beforeRewind, beforeSeek, seekEntry, rewindEntry,
      Program.asSubroutine_length, sought, retained, saved,
      GuardedCompiler.seekScratchInputFinish, rewindBitstringStart,
      Configuration.swapTapes, Configuration.resumeAt, Configuration.rebasePc,
      rewound, Nat.add_assoc]
      using rewindEmbedded
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, u' + v + w' + 1,
    by dsimp only [slots] at hw; omega, ((r₁.trans r₂).trans r₃).succ (final_step rewound), rfl, ?_, ?_⟩
  · simp [rewound, retained, saved, copiedBefore, rewindBitstringFinish,
      Configuration.resumeAt, Configuration.swapTapes, List.append_assoc]
  · simpa [Configuration.resumeAt, rewound] using hOutput

/-- Even malformed finite tapes pass through the same three scans and halt.
The bound includes the actual copying, forward scan, and output rewind. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 200 * (input.cells + output.cells + 1) ∧
      RunsFor program (DelimitedColumnSlotFill.entry input output) target used ∧
      target.halted = true := by
  obtain ⟨copied, u, hu, run₁, hHalt₁⟩ := DelimitedColumnSlotFill.runs_any input output
  obtain ⟨u', hu', embedded₁⟩ := run₁.withSubroutine_halted
    [] DelimitedColumnSlotFill.program
    (GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry ++
      OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) seekEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (DelimitedColumnSlotFill.entry input output)
      (copied.resumeAt seekEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded₁
  obtain ⟨sought, v, hv, run₂, hHalt₂, _hOutput₂⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape copied.inputTape copied.outputTape
  obtain ⟨v', hv', embedded₂⟩ := run₂.withSubroutine_halted beforeSeek
    GuardedCompiler.seekScratchInput
    (OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (copied.resumeAt seekEntry) (sought.resumeAt rewindEntry) v' := by
    simpa [second_layout, beforeSeek, seekEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  obtain ⟨rewound, w, hw, run₃, hHalt₃, _hInput₃⟩ :=
    OutputColumnRewind.toFirst_runs_any sought.inputTape sought.outputTape
  obtain ⟨w', hw', embedded₃⟩ := run₃.withSubroutine_halted beforeRewind
    OutputColumnRewind.toFirst [.halt] finalPc (Nat.zero_le _) rfl hHalt₃
  have r₃ : RunsFor program (sought.resumeAt rewindEntry) (rewound.resumeAt finalPc) w' := by
    simpa [third_layout, beforeRewind, beforeSeek, seekEntry, rewindEntry,
      Program.asSubroutine_length, Configuration.resumeAt, Configuration.rebasePc,
      Nat.add_assoc] using embedded₃
  have storage₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have storage₂ := GuardedCompiler.sourceStorage_le_of_run run₂
  have hRight : input.right.length ≤ input.cells := by simp [Tape.cells]
  have hLeft : sought.outputTape.left.length ≤ sought.outputTape.cells := by
    simp [Tape.cells]; omega
  simp only [GuardedCompiler.sourceStorage, DelimitedColumnSlotFill.entry] at storage₁
  simp only [GuardedCompiler.sourceStorage] at storage₂
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, u' + v' + w' + 1,
    by omega, ((r₁.trans r₂).trans r₃).succ (final_step rewound), rfl⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  have h₁ := Program.asSubroutine_no_randomBit DelimitedColumnSlotFill.program
    DelimitedColumnSlotFill.no_randomBit 0 seekEntry tape
  have h₂ := Program.asSubroutine_no_randomBit GuardedCompiler.seekScratchInput
    GuardedCompiler.seekScratchInput_no_randomBit seekEntry rewindEntry tape
  have hRewind : ∀ t, Instruction.randomBit t ∉ OutputColumnRewind.toFirst :=
    Program.swapTapes_no_randomBit rewindBitstring rewindBitstring_no_randomBit
  have h₃ := Program.asSubroutine_no_randomBit OutputColumnRewind.toFirst
    hRewind rewindEntry finalPc tape
  simpa only [program, beforeRewind, beforeSeek, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro (And.intro h₁ h₂) h₃)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (600 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hInitial : DelimitedColumnSlotFill.entry (Tape.ofBits raw) ({} : Tape) =
      Configuration.initial raw := rfl
  rw [hInitial] at run
  have hCells : (Tape.ofBits raw).cells ≤ raw.length + 1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit (by omega)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 600 * (length + 1),
    (PolynomiallyBounded.const 600).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChooseCandidatePowerPreparation
