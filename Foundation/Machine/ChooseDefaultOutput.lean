import Foundation.Machine.DuplicateDelimitedOutput
import Foundation.Machine.ChooseResponseParser

namespace Machine.ChooseDefaultOutput

private def tag : Program := [.write .output false, .moveRight .output]
private def finalPc : Nat := tag.length + DuplicateDelimitedOutput.program.length + 1

/-- Write the choose-stage tag and two copies of a stored generator.
Only the fixed tag and delimiter bits are constants; every generator bit is
read from the same retained input segment. No adversary state is appended. -/
def program : Program :=
  Program.withSubroutine tag DuplicateDelimitedOutput.program [.halt] finalPc

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = tag.length + DuplicateDelimitedOutput.program.length + 1 + 0 := by
      simp [finalPc]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

private theorem tag_run (input : Tape) (blanks : Nat) :
    RunsFor program ({ inputTape := input, outputTape := { right := List.replicate blanks none } } : Configuration)
      ({ pc := 2, inputTape := input,
         outputTape := { left := [some false], right := List.replicate (blanks-1) none } } : Configuration) 2 := by
  let written : Configuration :=
    { pc := 1, inputTape := input, outputTape := { current := some false, right := List.replicate blanks none } }
  have hWrite : Step program
      ({ inputTape := input, outputTape := { right := List.replicate blanks none } } : Configuration) written := by
    simp [Step, successors, next, program, tag, written, Program.withSubroutine,
      Instruction.next, Configuration.advance, Configuration.updateTape, Tape.write]
  have hMove : Step program written
      ({ pc := 2, inputTape := input,
         outputTape := { left := [some false], right := List.replicate (blanks-1) none } } : Configuration) := by
    cases blanks <;> simp [Step, successors, next, program, tag, written, Program.withSubroutine,
      Instruction.next, Configuration.advance, Configuration.updateTape, Tape.moveRight, List.replicate_succ]
  exact ((RunsFor.zero _).succ hWrite).succ hMove

/-- Native fallback payload correctness once the represented instance's
generator has been isolated between actual blank separators. The result is
the canonical generator pair with empty state; it is not a decoded value
written by a meta-level operation. -/
theorem runs_generator (before tail : List (Option Bool)) (generator : List Bool) (blanks : Nat) :
    ∃ target used,
      RunsFor program (writeDelimitedContextStart (none::before) [] tail generator blanks) target used ∧
      target.halted = true ∧ target.outputBits = canonicalMessageBits generator generator [] := by
  let source := writeDelimitedContextStart (none::before) [] tail generator blanks
  let tagged : Configuration :=
    { pc := 2, inputTape := source.inputTape,
      outputTape := { left := [some false], right := List.replicate (blanks-1) none } }
  have r₁ : RunsFor program source tagged 2 := tag_run source.inputTape blanks
  obtain ⟨copied, used, run, hHalt, _, hOutput⟩ :=
    DuplicateDelimitedOutput.runs_bits before [some false] tail generator (blanks-1)
  obtain ⟨used', _, embedded⟩ := run.withSubroutine_halted
    tag DuplicateDelimitedOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt
  have hCall : tagged =
      (writeDelimitedContextStart (none::before) [some false] tail generator (blanks-1)).rebasePc tag.length := rfl
  have r₂ : RunsFor program tagged (copied.resumeAt finalPc) used' := by
    rw [hCall]
    exact embedded
  refine ⟨{ copied.resumeAt finalPc with halted := true }, 2+used'+1,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl, ?_⟩
  have hBits := hOutput.bits
  simpa [Configuration.outputBits, Configuration.resumeAt, Tape.bits, canonicalMessageBits,
    List.reverse_append, List.map_append, List.append_assoc] using hBits

/-- Caller-context termination for the fallback writer. Even arbitrary
input separators and arbitrary pre-existing output cells cannot make its
finite scans diverge. Correct fallback contents still require the generator
layout of `runs_generator`. -/
theorem runs_tapes (input output : Tape) :
    ∃ target used, used ≤ 10000*(input.cells+output.cells+1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration) target used ∧
      target.halted = true := by
  let written : Configuration := { pc := 1, inputTape := input, outputTape := output.write (some false) }
  let tagged : Configuration := { pc := 2, inputTape := input, outputTape := (output.write (some false)).moveRight }
  have hWrite : Step program ({ inputTape := input, outputTape := output } : Configuration) written := by
    simp [Step, successors, next, program, tag, written, Program.withSubroutine,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  have hMove : Step program written tagged := by
    simp [Step, successors, next, program, tag, written, tagged, Program.withSubroutine,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration) tagged 2 :=
    ((RunsFor.zero _).succ hWrite).succ hMove
  obtain ⟨copied, used, hUsed, run, hHalt⟩ :=
    DuplicateDelimitedOutput.runs_any tagged.inputTape tagged.outputTape
  obtain ⟨used', hUsed', embedded⟩ := run.withSubroutine_halted
    tag DuplicateDelimitedOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt
  have r₂ : RunsFor program tagged (copied.resumeAt finalPc) used' := embedded
  refine ⟨{ copied.resumeAt finalPc with halted := true }, 2+used'+1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  have hs := GuardedCompiler.sourceStorage_le_of_run r₁
  simp only [GuardedCompiler.sourceStorage] at hs
  omega

/-- Every finite raw input also stops under the same finite fallback code.
Its generator interpretation still requires the isolated-segment premise
of the correctness theorem. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 10000*(raw.length+1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  let tagged : Configuration := { pc := 2, inputTape := Tape.ofBits raw, outputTape := { left := [some false] } }
  have r₁ : RunsFor program (Configuration.initial raw) tagged 2 := tag_run (Tape.ofBits raw) 0
  obtain ⟨copied, used, hUsed, run, hHalt⟩ :=
    DuplicateDelimitedOutput.runs_any (Tape.ofBits raw) ({ left := [some false] } : Tape)
  obtain ⟨used', hUsed', embedded⟩ := run.withSubroutine_halted
    tag DuplicateDelimitedOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt
  have r₂ : RunsFor program tagged (copied.resumeAt finalPc) used' := embedded
  refine ⟨{ copied.resumeAt finalPc with halted := true }, 2+used'+1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  have hCells : (Tape.ofBits raw).cells ≤ raw.length+1 := by cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hOutput : ({ left := [some false] } : Tape).cells = 2 := rfl
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (10000*(raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 10000*(m+1), (PolynomiallyBounded.const 10000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChooseDefaultOutput
