import Foundation.Crypto.Semantics.Machine.BitstringErasure
import Foundation.Crypto.Semantics.Machine.BitstringRewind
import Foundation.Crypto.Semantics.Machine.NativeInvocation
import Foundation.Crypto.Semantics.Machine.StoredGuessLayout

namespace Machine.ChoosePowerReset

private def outputErase : Program := eraseOutputBlocks 2
private def inputErase : Program := eraseOutputBlock.swapTapes
private def eraseEntry : Nat := outputErase.length + 1
private def rewindEntry : Nat := eraseEntry + inputErase.length + 1
private def finalPc : Nat := rewindEntry + rewindBitstring.length + 1
private def beforeErase : Program := outputErase.asSubroutine 0 eraseEntry
private def beforeRewind : Program := beforeErase ++ inputErase.asSubroutine eraseEntry rewindEntry

/-- Remove the two actual guarded-call scratch blocks, erase the returned
status before the protected response, and rewind that original request.
This is finite tape code; it does not reconstruct a request from decoded data. -/
def program : Program := beforeRewind ++ rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] outputErase
      (inputErase.asSubroutine eraseEntry rewindEntry ++
        rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) eraseEntry := by
  simp [program, beforeRewind, beforeErase, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine beforeErase inputErase
      (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry := by
  simp [program, beforeRewind, beforeErase, Program.withSubroutine,
    eraseEntry, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine beforeRewind rewindBitstring [.halt] finalPc := by
  simp [program, beforeRewind, beforeErase, Program.withSubroutine,
    eraseEntry, rewindEntry, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc) { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    rw [third_layout]
    have hIndex : finalPc = beforeRewind.length + rewindBitstring.length + 1 + 0 := by
      simp [finalPc, beforeRewind, beforeErase, eraseEntry, rewindEntry,
        Program.asSubroutine_length, Nat.add_assoc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, Configuration.resumeAt, hLookup, Instruction.next]

/-- Physical post-call layout: the status on the saved-request tape and
its duplicate plus guarded source scratch on the other tape. -/
def start (request scratch : List Bool) (status : Bool) (padding : Nat) : Configuration :=
  { inputTape := { left := some status :: none :: request.reverse.map some, right := List.replicate padding none },
    outputTape := { left := savedOutputBlocks [[status], scratch] } }

/-- Every saved request is recovered by native erasure and rewind. The final
record may contain explicit outer blanks, which are compared cell by cell.
The same request, including all adversary state bits, is preserved. -/
theorem runs_saved (request scratch : List Bool) (status : Bool) (padding : Nat) :
    ∃ target used,
      used ≤ eraseOutputBlocksSteps [[status], scratch] + 7 +
        (2 * request.length + 4) + 1 ∧
      RunsFor program (start request scratch status padding) target used ∧
      target.halted = true ∧
      (target.resumeAt 0).Equivalent (Configuration.initial request) := by
  let input : Tape := { left := some status :: none :: request.reverse.map some, right := List.replicate padding none }
  let cleaned := eraseOutputBlocksFinish input [] [[status], scratch] []
  have eval₁ := eraseOutputBlocks_eval input [] [[status], scratch] []
  have hSupport : cleaned ∈ (evalConfigWithin outputErase
      (start request scratch status padding)
      (eraseOutputBlocksSteps [[status], scratch])).support := by
    have hStart : start request scratch status padding =
        eraseOutputBlocksStart input [] [[status], scratch] [] := by
      simp [start, input, eraseOutputBlocksStart]
    rw [hStart]
    change cleaned ∈ (evalConfigWithin (eraseOutputBlocks 2)
      (eraseOutputBlocksStart input [] [[status], scratch] [])
      (eraseOutputBlocksSteps [[status], scratch])).support
    have hEval : evalConfigWithin (eraseOutputBlocks 2)
        (eraseOutputBlocksStart input [] [[status], scratch] [])
        (eraseOutputBlocksSteps [[status], scratch]) = PMF.pure cleaned := by
      simpa only [List.length_cons, List.length_nil] using eval₁
    rw [hEval]
    simp
  obtain ⟨u, hu, run₁⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  obtain ⟨u', hu', embedded₁⟩ := run₁.withSubroutine_halted [] outputErase
    (inputErase.asSubroutine eraseEntry rewindEntry ++
      rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) eraseEntry
    (Nat.zero_le _) rfl rfl
  have r₁ : RunsFor program (start request scratch status padding)
      (cleaned.resumeAt eraseEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded₁
  let erased := (eraseOutputBlockFinish cleaned.outputTape (request.reverse.map some)
    [status] (List.replicate padding none)).swapTapes
  have run₂ := (eraseOutputBlock_runs cleaned.outputTape (request.reverse.map some)
    [status] (List.replicate padding none)).swapTapes
  change RunsFor inputErase (cleaned.resumeAt 0) erased 7 at run₂
  obtain ⟨v, hv, embedded₂⟩ := run₂.withSubroutine_halted beforeErase inputErase
    (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry
    (by simp [Configuration.resumeAt]) rfl rfl
  have r₂ : RunsFor program (cleaned.resumeAt eraseEntry) (erased.resumeAt rewindEntry) v := by
    simpa [second_layout, beforeErase, eraseEntry, Program.asSubroutine_length,
      cleaned, input, erased, start, eraseOutputBlocksFinish,
      eraseOutputBlockStart, eraseOutputBlockFinish,
      Configuration.swapTapes, Configuration.resumeAt, Configuration.rebasePc]
      using embedded₂
  let canonical := rewindBitstringStart request cleaned.outputTape
  let returned := rewindBitstringFinish request cleaned.outputTape
  have hLayout : (canonical.rebasePc beforeRewind.length).Equivalent
      (erased.resumeAt rewindEntry) := by
    refine ⟨?_, rfl, ?_, Tape.Equivalent.refl _⟩
    · simp [canonical, rewindBitstringStart, Configuration.rebasePc,
        Configuration.resumeAt, beforeRewind, beforeErase, eraseEntry, rewindEntry,
        Program.asSubroutine_length, Nat.add_assoc]
    · change ({ left := request.reverse.map some } : Tape).Equivalent
        (eraseOutputBlockFinish cleaned.outputTape (request.reverse.map some)
          [status] (List.replicate padding none)).outputTape
      change ({ left := request.reverse.map some } : Tape).Equivalent
        { left := request.reverse.map some,
          right := List.replicate 2 none ++ List.replicate padding none }
      rw [← List.replicate_add]
      exact (Tape.blank_padding_equivalent _ _).symm
  obtain ⟨actual, w, hw, run₃, hReturned⟩ := nativeCall_of_eval beforeRewind
    rewindBitstring [.halt] finalPc canonical returned (erased.resumeAt rewindEntry)
    (2 * request.length + 4) (Nat.zero_le _) rfl rfl
    ((rewindBitstring_runs request cleaned.outputTape).evalConfigWithin_eq_pure_of_no_randomBit
      rewindBitstring_no_randomBit) hLayout
  have hPc : actual.pc = finalPc := by simpa [Configuration.resumeAt] using hReturned.1.symm
  have hActive : actual.halted = false := hReturned.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have r := final_step actual
    have hResume : actual.resumeAt finalPc = actual := by
      cases actual
      simp_all [Configuration.resumeAt]
    rw [hResume] at r
    exact r
  have hBlank : cleaned.outputTape.Equivalent ({} : Tape) := by
    change ({ left := [], right :=
      List.replicate (([[status], scratch].map List.length).sum + 2) none ++ [] } : Tape).Equivalent {}
    simpa using Tape.blank_padding_equivalent [] ((([[status], scratch].map List.length).sum) + 2)
  refine ⟨{ actual with halted := true }, u' + v + w + 1, by omega,
    ((r₁.trans r₂).trans run₃).succ hLast, rfl, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact hReturned.2.2.1.symm.trans (rewindBitstringFinish_input_equivalent request cleaned.outputTape)
  · exact hReturned.2.2.2.symm.trans hBlank

/-- The reset precondition is the layout returned by the actual guarded
opposite-tape call. The arithmetic input has an explicit protected blank
boundary, and the saved request is separated from its one-bit status. -/
theorem returned_start (core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status]) :
    ((GuardedCompiler.rawResultFrom core columns [none]
      (none :: request.reverse.map some) c).swapTapes).resumeAt 0 =
    start request (GuardedCompiler.storedSourceScratchBits columns c.inputTape) status
      (2 * c.outputTape.cells + 2 - 1) := by
  let returned := (GuardedCompiler.rawResultFrom core columns [none]
    (none :: request.reverse.map some) c).swapTapes
  have hInput : returned.inputTape =
      ({ left := some status :: none :: request.reverse.map some,
         right := List.replicate (2 * c.outputTape.cells + 2 - 1) none } : Tape) := by
    change ({ left := c.outputBits.reverse.map some ++ none :: request.reverse.map some,
              right := List.replicate (2 * c.outputTape.cells + 2 - c.outputBits.length) none } : Tape) = _
    rw [hStatus]
    rfl
  have hLeft := GuardedCompiler.rawResultFrom_output_storedBlocks core columns []
    (none :: request.reverse.map some) c
  have hOutput : returned.outputTape =
      ({ left := savedOutputBlocks [[status],
          GuardedCompiler.storedSourceScratchBits columns c.inputTape] } : Tape) := by
    change c.outputBits.reverse.map some ++
        GuardedCompiler.scratchPrefix (columns.reverse.map some ++ [none]) c.inputTape = _ at hLeft
    change ({ left := c.outputBits.reverse.map some ++
      GuardedCompiler.scratchPrefix (columns.reverse.map some ++ [none]) c.inputTape } : Tape) = _
    rw [hLeft, hStatus]
    simp
  change ({ inputTape := returned.inputTape, outputTape := returned.outputTape } : Configuration) = _
  rw [hInput, hOutput]
  rfl

/-- The retained scratch is part of the actual returned output, so its
size can be charged to the check trace without an extra source-size premise. -/
theorem scratch_length_le_returned_outputBits (core : Program)
    (columns request : List Bool) (c : Configuration) (status : Bool)
    (hStatus : c.outputBits = [status]) :
    (GuardedCompiler.storedSourceScratchBits columns c.inputTape).length ≤
      (((GuardedCompiler.rawResultFrom core columns [none]
        (none :: request.reverse.map some) c).swapTapes).resumeAt 0).outputBits.length := by
  rw [returned_start core columns request c status hStatus]
  simp [start, Configuration.outputBits, Tape.bits, savedOutputBlocks,
    List.reverse_append, List.filterMap_append, List.filterMap_map]

/-- Erase the actual guarded result and recover the original saved request,
so a second candidate can be inspected using the same input. The source
configuration comes from `rawResultFrom`, not from a new tape fixture. -/
theorem runs_returned (core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status]) :
    ∃ target used,
      used ≤ eraseOutputBlocksSteps [[status],
        GuardedCompiler.storedSourceScratchBits columns c.inputTape] + 7 +
          (2 * request.length + 4) + 1 ∧
      RunsFor program
        (((GuardedCompiler.rawResultFrom core columns [none]
          (none :: request.reverse.map some) c).swapTapes).resumeAt 0) target used ∧
      target.halted = true ∧
      (target.resumeAt 0).Equivalent (Configuration.initial request) := by
  rw [returned_start core columns request c status hStatus]
  exact runs_saved request (GuardedCompiler.storedSourceScratchBits columns c.inputTape)
    status (2 * c.outputTape.cells + 2 - 1)

/-- All three scans terminate on arbitrary finite tapes, including missing
separators and malformed saved blocks. No decoded-response assumption enters
the time bound. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 40 * (input.cells + output.cells + 1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  obtain ⟨cleaned, u, hu, run₁, hHalt₁, hInput₁, _hLeft₁⟩ :=
    eraseOutputBlocks_terminates_from_anyTape 2 input output
  obtain ⟨u', hu', embedded₁⟩ := run₁.withSubroutine_halted [] outputErase
    (inputErase.asSubroutine eraseEntry rewindEntry ++
      rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) eraseEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (cleaned.resumeAt eraseEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded₁
  obtain ⟨erasedOpposite, v, hv, oppositeRun, hHalt₂, _hInput₂, hLeft₂⟩ :=
    eraseOutputBlock_terminates_from_anyTape cleaned.outputTape cleaned.inputTape
  let erased := erasedOpposite.swapTapes
  have run₂ : RunsFor inputErase
      ({ inputTape := cleaned.inputTape, outputTape := cleaned.outputTape } : Configuration)
      erased v := by
    simpa [inputErase, erased, Configuration.swapTapes] using oppositeRun.swapTapes
  have hErasedHalt : erased.halted = true := hHalt₂
  obtain ⟨v', hv', embedded₂⟩ := run₂.withSubroutine_halted beforeErase inputErase
    (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry
    (Nat.zero_le _) rfl hErasedHalt
  have r₂ : RunsFor program (cleaned.resumeAt eraseEntry) (erased.resumeAt rewindEntry) v' := by
    simpa [second_layout, beforeErase, eraseEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  obtain ⟨rewound, w, hw, run₃, hHalt₃, _hOutput₃⟩ :=
    rewindBitstring_terminates_from erased.inputTape erased.outputTape
  obtain ⟨w', hw', embedded₃⟩ := run₃.withSubroutine_halted beforeRewind
    rewindBitstring [.halt] finalPc (Nat.zero_le _) rfl hHalt₃
  have r₃ : RunsFor program (erased.resumeAt rewindEntry) (rewound.resumeAt finalPc) w' := by
    simpa [third_layout, beforeRewind, beforeErase, eraseEntry, rewindEntry,
      Program.asSubroutine_length, Configuration.resumeAt, Configuration.rebasePc,
      Nat.add_assoc] using embedded₃
  have hInputLeft : input.left.length ≤ input.cells := by simp [Tape.cells]; omega
  have hOutputLeft : output.left.length ≤ output.cells := by simp [Tape.cells]; omega
  have hErasedLeft : erased.inputTape.left.length ≤ input.left.length := by
    simpa [erased, Configuration.swapTapes, hInput₁] using hLeft₂
  rw [hInput₁] at hv
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, u' + v' + w' + 1,
    by omega, ((r₁.trans r₂).trans r₃).succ (final_step rewound), rfl⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  have h₁ := Program.asSubroutine_no_randomBit outputErase
    (eraseOutputBlocks_no_randomBit 2) 0 eraseEntry tape
  have hSwap := Program.swapTapes_no_randomBit eraseOutputBlock eraseOutputBlock_no_randomBit
  have h₂ := Program.asSubroutine_no_randomBit inputErase hSwap eraseEntry rewindEntry tape
  have h₃ := Program.asSubroutine_no_randomBit rewindBitstring
    rewindBitstring_no_randomBit rewindEntry finalPc tape
  simpa only [program, beforeRewind, beforeErase, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro (And.intro h₁ h₂) h₃)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (120 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hInitial : ({ inputTape := Tape.ofBits raw, outputTape := ({} : Tape) } : Configuration) =
      Configuration.initial raw := rfl
  rw [hInitial] at run
  have hCells : (Tape.ofBits raw).cells ≤ raw.length + 1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit (by omega)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 120 * (length + 1),
    (PolynomiallyBounded.const 120).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChoosePowerReset
