import Foundation.Machine.BitstringCopy
import Foundation.Machine.GuardedOutput
import Foundation.Machine.OutputColumnRewind
import Foundation.Machine.NativeInvocation

namespace Machine.ChooseRequestPreparation

private def requestEntry (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def seekEntry : Nat := copyBitstring.length + 1
private def rewindEntry : Nat := seekEntry + GuardedCompiler.seekScratchInput.length + 1
private def finalPc : Nat := rewindEntry + OutputColumnRewind.toFirst.length + 1
private def beforeSeek : Program := copyBitstring.asSubroutine 0 seekEntry
private def beforeRewind : Program := beforeSeek ++
  GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry

/-- Copy the complete finite request, preserve its original cells behind
an actual blank separator, and rewind the copied request on the opposite
tape. Subsequent guarded checks can erase their scratch without losing the
original request, including its unexamined response state. -/
def program : Program := beforeRewind ++
  OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] copyBitstring
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

/-- Every finite raw request is copied by real transitions. The saved
request is exact, while rewind may leave irrelevant outer blank padding. -/
theorem runs_request (raw : List Bool) :
    ∃ target used, used ≤ 8 * raw.length + 10 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape = ({ left := none :: raw.reverse.map some } : Tape) ∧
      target.outputTape.Equivalent (Tape.ofBits raw) := by
  let copied := copyBitstringFinish raw
  obtain ⟨u, hu, embedded₁⟩ := (copyBitstring_runs raw).withSubroutine_halted
    [] copyBitstring
    (GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry ++
      OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) seekEntry
    (Nat.zero_le _) rfl rfl
  have r₁ : RunsFor program (Configuration.initial raw)
      (copied.resumeAt seekEntry) u := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add, requestEntry]
      using embedded₁
  let sought := GuardedCompiler.seekScratchInputFinish (raw.reverse.map some) []
    ({ left := raw.reverse.map some } : Tape)
  have seekRun := GuardedCompiler.seekScratchInput_runs (raw.reverse.map some) []
    ({ left := raw.reverse.map some } : Tape)
  change RunsFor GuardedCompiler.seekScratchInput (copied.resumeAt 0) sought 3 at seekRun
  obtain ⟨v, hv, embedded₂⟩ := seekRun.withSubroutine_halted beforeSeek
    GuardedCompiler.seekScratchInput
    (OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry
    (Nat.zero_le _) rfl rfl
  have r₂ : RunsFor program (copied.resumeAt seekEntry) (sought.resumeAt rewindEntry) v := by
    simpa [second_layout, beforeSeek, seekEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  let saved : Tape := { left := none :: raw.reverse.map some }
  obtain ⟨w, hw, rewindRun, hOutput⟩ := OutputColumnRewind.toFirst_runs raw saved
  let rewound := (rewindBitstringFinish raw saved).swapTapes
  obtain ⟨w', hw', embedded₃⟩ := rewindRun.withSubroutine_halted beforeRewind
    OutputColumnRewind.toFirst [.halt] finalPc (Nat.zero_le _) rfl rfl
  have r₃ : RunsFor program (sought.resumeAt rewindEntry) (rewound.resumeAt finalPc) w' := by
    simpa [third_layout, beforeRewind, beforeSeek, seekEntry, rewindEntry,
      Program.asSubroutine_length, sought, saved, GuardedCompiler.seekScratchInputFinish,
      rewindBitstringStart, Configuration.swapTapes, Configuration.resumeAt,
      Configuration.rebasePc, rewound, Nat.add_assoc] using embedded₃
  have hCopyBound := copyBitstringSteps_le raw
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, u + v + w' + 1,
    by omega, ((r₁.trans r₂).trans r₃).succ (final_step rewound), rfl, ?_, ?_⟩
  · rfl
  · simpa [Configuration.resumeAt, rewound] using hOutput

/-- All finite physical tapes pass through the same three scans and halt.
The bound includes the actual copying, forward scan, and output rewind. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 200 * (input.cells + output.cells + 1) ∧
      RunsFor program (requestEntry input output) target used ∧
      target.halted = true := by
  obtain ⟨copied, u, hu, run₁, hHalt₁⟩ := copyBitstring_terminates_from_anyTape input output
  obtain ⟨u', hu', embedded₁⟩ := run₁.withSubroutine_halted
    [] copyBitstring
    (GuardedCompiler.seekScratchInput.asSubroutine seekEntry rewindEntry ++
      OutputColumnRewind.toFirst.asSubroutine rewindEntry finalPc ++ [.halt]) seekEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (requestEntry input output)
      (copied.resumeAt seekEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add, requestEntry]
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
  simp only [GuardedCompiler.sourceStorage] at storage₁
  simp only [GuardedCompiler.sourceStorage] at storage₂
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, u' + v' + w' + 1,
    by omega, ((r₁.trans r₂).trans r₃).succ (final_step rewound), rfl⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  have h₁ := Program.asSubroutine_no_randomBit copyBitstring
    copyBitstring_no_randomBit 0 seekEntry tape
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
  have hInitial : requestEntry (Tape.ofBits raw) ({} : Tape) =
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

end Machine.ChooseRequestPreparation
