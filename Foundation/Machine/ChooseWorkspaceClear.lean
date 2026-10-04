import Foundation.Machine.GuardedOutput
import Foundation.Machine.BitstringErasure
import Foundation.Machine.GuardedTrace
import Foundation.Machine.TapeSwap

namespace Machine.ChooseWorkspaceClear

private def seek : Program := GuardedCompiler.seekScratchInput.swapTapes
private def backEntry : Nat := seek.length+1
private def eraseEntry : Nat := backEntry+1
private def finalPc : Nat := eraseEntry+eraseOutputBlock.length+1
private def beforeErase : Program := seek.asSubroutine 0 backEntry ++ [.moveLeft .output]

/-- Clear a contiguous copied instance and its status after the caller has
selected a continuation. Every frontier search, move, and erasure is a
native instruction. The original request on the input tape is untouched. -/
def program : Program := Program.withSubroutine beforeErase eraseOutputBlock [.halt] finalPc

private theorem first_layout : program =
    Program.withSubroutine [] seek
      ([.moveLeft .output] ++ eraseOutputBlock.asSubroutine eraseEntry finalPc ++ [.halt]) backEntry := by
  simp [program, beforeErase, Program.withSubroutine, eraseEntry, backEntry,
    Program.asSubroutine_length, List.append_assoc]

private theorem back_step (c : Configuration) (hPc : c.pc = backEntry)
    (hActive : c.halted = false) :
    Step program c { c with pc := eraseEntry, outputTape := c.outputTape.moveLeft } := by
  have hLookup : program[backEntry]? = some (.moveLeft .output) := by
    rw [first_layout]
    have hIndex : backEntry = [].length+seek.length+1+0 := rfl
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next,
    Configuration.advance, Configuration.updateTape, eraseEntry]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = beforeErase.length+eraseOutputBlock.length+1+0 := by
      simp [finalPc, beforeErase, backEntry, eraseEntry, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Clear the actual status and copied code even when the head is inside
the contiguous block. The caller's input is preserved cell for cell. This
layout premise is essential: termination alone does not erase separated
blocks beyond an internal blank. -/
theorem runs_bits (beforeBits remaining : List Bool) (input : Tape) :
    let start : Configuration :=
      { inputTape := input,
        outputTape := { Tape.ofBits remaining with left := beforeBits.reverse.map some ++ [none] } }
    ∃ target used,
      RunsFor program start target used ∧ target.halted = true ∧
      target.inputTape = input ∧ target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let before := beforeBits.reverse.map some ++ [none]
  have run₁ := (GuardedCompiler.seekScratchInput_runs before remaining input).swapTapes
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted [] seek
    ([.moveLeft .output] ++ eraseOutputBlock.asSubroutine eraseEntry finalPc ++ [.halt])
    backEntry (Nat.zero_le _) rfl rfl
  let sought := (GuardedCompiler.seekScratchInputFinish before remaining input).swapTapes
  let source : Configuration :=
    { inputTape := input, outputTape := { Tape.ofBits remaining with left := before } }
  have r₁ : RunsFor program source (sought.resumeAt backEntry) v₁ := by
    rw [first_layout]
    exact embedded₁
  let backed : Configuration :=
    { sought.resumeAt backEntry with pc := eraseEntry, outputTape := sought.outputTape.moveLeft }
  have rBack : RunsFor program (sought.resumeAt backEntry) backed 1 :=
    (RunsFor.zero _).succ (back_step _ rfl rfl)
  have hEraseStart : eraseOutputBlockStart input [] (beforeBits ++ remaining) [none] = backed.resumeAt 0 := by
    simp [eraseOutputBlockStart, backed, sought, before, GuardedCompiler.seekScratchInputFinish,
      Configuration.swapTapes, Configuration.resumeAt, Tape.moveLeft,
      List.reverse_append, List.map_append, List.append_assoc]
    change (
      { inputTape := input
        outputTape :=
          { left := (remaining.reverse ++ beforeBits.reverse).map some ++ [none]
            right := [none] } } : Configuration) = _
    simp only [List.map_append, List.map_reverse, List.append_assoc]
  have run₂ := eraseOutputBlock_runs input [] (beforeBits ++ remaining) [none]
  rw [hEraseStart] at run₂
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted beforeErase eraseOutputBlock [.halt]
    finalPc (Nat.zero_le _) rfl rfl
  let cleared := eraseOutputBlockFinish input [] (beforeBits ++ remaining) [none]
  have hEntry : (backed.resumeAt 0).rebasePc beforeErase.length = backed := by
    simp [beforeErase, backEntry, eraseEntry, Program.asSubroutine_length,
      backed, Configuration.resumeAt, Configuration.rebasePc]
  have r₂ : RunsFor program backed (cleared.resumeAt finalPc) v₂ := by
    unfold program
    simpa only [hEntry] using embedded₂
  refine ⟨{ cleared.resumeAt finalPc with halted := true }, v₁+1+v₂+1,
    ((r₁.trans rBack).trans r₂).succ (final_step _ rfl rfl), rfl, rfl, ?_⟩
  change ({ right := List.replicate ((beforeBits++remaining).reverse.length+1) none ++ [none] } : Tape).Equivalent {}
  have hPadding := Tape.blank_padding_equivalent [] ((beforeBits++remaining).reverse.length+2)
  have hRep : List.replicate ((beforeBits++remaining).reverse.length+1) (none : Option Bool) ++ [none] =
      List.replicate ((beforeBits++remaining).reverse.length+2) none := by
    rw [show ([none] : List (Option Bool)) = List.replicate 1 none from rfl,
      ← List.replicate_add]
  rw [hRep]
  exact hPadding

/-- Every finite physical input/output pair terminates. This certificate
charges actual storage after the frontier scan and preserves the input. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 100*(input.cells+output.cells+1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration) target used ∧
      target.halted = true ∧ target.inputTape = input := by
  obtain ⟨sought, u₁, hu₁, run₁, hHalt₁, hInput₁⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape output input
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.swapTapes.withSubroutine_halted [] seek
    ([.moveLeft .output] ++ eraseOutputBlock.asSubroutine eraseEntry finalPc ++ [.halt])
    backEntry (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (sought.swapTapes.resumeAt backEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, Configuration.swapTapes] using embedded₁
  let backed : Configuration :=
    { sought.swapTapes.resumeAt backEntry with pc := eraseEntry, outputTape := sought.inputTape.moveLeft }
  have rBack : RunsFor program (sought.swapTapes.resumeAt backEntry) backed 1 :=
    (RunsFor.zero _).succ (back_step _ rfl rfl)
  obtain ⟨cleared, u₂, hu₂, run₂, hHalt₂, hInput₂, _⟩ :=
    eraseOutputBlock_terminates_from_anyTape backed.inputTape backed.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted beforeErase eraseOutputBlock [.halt]
    finalPc (Nat.zero_le _) rfl hHalt₂
  have hEntry : ({ inputTape := backed.inputTape, outputTape := backed.outputTape } : Configuration).rebasePc
      beforeErase.length = backed := by
    simp [beforeErase, backEntry, eraseEntry, Program.asSubroutine_length,
      backed, Configuration.swapTapes, Configuration.resumeAt, Configuration.rebasePc]
  have r₂ : RunsFor program backed (cleared.resumeAt finalPc) v₂ := by
    unfold program
    simpa only [hEntry] using embedded₂
  refine ⟨{ cleared.resumeAt finalPc with halted := true }, v₁+1+v₂+1, ?_,
    ((r₁.trans rBack).trans r₂).succ (final_step _ rfl rfl), rfl, ?_⟩
  · have hs₁ := GuardedCompiler.sourceStorage_le_of_run r₁
    have hsBack := GuardedCompiler.sourceStorage_le_of_run rBack
    have hLeft : backed.outputTape.left.length ≤ backed.outputTape.cells := by
      simp only [Tape.cells]; omega
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt, Configuration.swapTapes] at hs₁ hsBack
    omega
  · exact hInput₂.trans hInput₁

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

/-- The shaped erasure result also enjoys the universal physical-storage
bound. Both certificates refer to the same deterministic native execution. -/
theorem runs_bits_bounded (beforeBits remaining : List Bool) (input : Tape) :
    let output : Tape := { Tape.ofBits remaining with left := beforeBits.reverse.map some ++ [none] }
    ∃ (target : Configuration) (used : Nat), used ≤ 100*(input.cells+output.cells+1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration) target used ∧
      target.halted = true ∧ target.inputTape = input ∧ target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  obtain ⟨shaped, a, shapedRun, shapedHalt, _, shapedOutput⟩ := runs_bits beforeBits remaining input
  obtain ⟨target, used, hUsed, run, hHalt, hInput⟩ := runs_any input _
  have same := run.halted_finish_eq_of_no_randomBit shapedRun hHalt shapedHalt no_randomBit
  exact ⟨target, used, hUsed, run, hHalt, hInput, same ▸ shapedOutput⟩

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (300*(raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt, _⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hCells : (Tape.ofBits raw).cells ≤ raw.length+1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 300*(m+1), (PolynomiallyBounded.const 300).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChooseWorkspaceClear
