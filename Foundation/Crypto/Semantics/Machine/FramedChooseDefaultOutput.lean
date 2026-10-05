import Foundation.Crypto.Semantics.Machine.FramedExponentPreparation
import Foundation.Crypto.Semantics.Machine.InstanceGeneratorIsolation
import Foundation.Crypto.Semantics.Machine.ChooseDefaultOutput

namespace Machine.FramedChooseDefaultOutput

private def isolationEntry : Nat := FramedExponentPreparation.program.length + 1
private def writeEntry : Nat := isolationEntry + InstanceGeneratorIsolation.program.length + 1
private def finalPc : Nat := writeEntry + ChooseDefaultOutput.program.length + 1
private def first : Program := FramedExponentPreparation.program.asSubroutine 0 isolationEntry
private def second : Program := InstanceGeneratorIsolation.program.asSubroutine isolationEntry writeEntry

/-- Actual fallback output from a framed request: locate the original
instance generator, isolate its stored bits with native tape operations,
and emit the generator pair with empty state. The acceptance decision is
made by the enclosing normalizer; this code implements only its fallback. -/
def program : Program :=
  first ++ second ++ ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedExponentPreparation.program
      (second ++ ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) isolationEntry := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first InstanceGeneratorIsolation.program
      (ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) writeEntry := by
  simp [program, second, first, isolationEntry, Program.asSubroutine_length,
    Program.withSubroutine, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) ChooseDefaultOutput.program [.halt] finalPc := by
  simp [program, first, second, isolationEntry, writeEntry, Program.asSubroutine_length,
    Program.withSubroutine, List.append_assoc, Nat.add_assoc]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    rw [third_layout]
    have hIndex : finalPc = (first ++ second).length + ChooseDefaultOutput.program.length + 1 + 0 := by
      simp [finalPc, first, second, writeEntry, isolationEntry, Program.asSubroutine_length, Nat.add_assoc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Every reply, including an arbitrary malformed choose response, yields
the same canonical fallback once the represented instance fields have their
required widths. Every emitted generator bit comes from that actual framed
instance; no fresh mathematical tape is substituted into the execution. -/
theorem runs_valid (n : Nat) (modulus exponent generator reply : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    ∃ target used,
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++
          frame (modulus ++ exponent ++ generator) ++ frame reply)) target used ∧
      target.halted = true ∧ target.outputBits = canonicalMessageBits generator generator [] := by
  let base := modulus.reverse.map some ++
    some false :: List.replicate (modulus ++ exponent ++ generator).length (some true) ++
      some false :: List.replicate n (some true)
  let columns := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
  obtain ⟨prepared, u₁, _, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent generator (frame reply) hModulus hExponent
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedExponentPreparation.program
    (second ++ ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) isolationEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++
        frame (modulus ++ exponent ++ generator) ++ frame reply))
      (prepared.resumeAt isolationEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  have hNonempty : exponent.reverse ≠ [] := by
    intro h
    have hLength := congrArg List.length h
    simp only [List.length_reverse, List.length_nil] at hLength
    omega
  cases hReverse : exponent.reverse with
  | nil => exact False.elim (hNonempty hReverse)
  | cons last rest =>
    let before := rest.map some ++ base
    obtain ⟨isolated, u₂, run₂, hHalt₂, hReady₂⟩ :=
      InstanceGeneratorIsolation.runs_generator (List.replicate modulus.length false)
        exponent modulus generator (frame reply) (by simp) hExponent hGenerator (some last) before
    obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted
      first InstanceGeneratorIsolation.program
      (ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) writeEntry
      (Nat.zero_le _) rfl hHalt₂
    let start : Configuration :=
      { inputTape := { Tape.ofBits (generator ++ frame reply) with left := some last :: before },
        outputTape := { left := none :: columns.reverse.map some } }
    have hCall : (start.rebasePc first.length).Equivalent (prepared.resumeAt isolationEntry) := by
      refine ⟨?_, rfl, ?_, hOutput₁.symm⟩
      · simp [start, first, isolationEntry, Configuration.rebasePc, Configuration.resumeAt,
          Program.asSubroutine_length]
      · have h := hInput₁.symm
        rw [hReverse] at h
        simpa only [start, before, base, Configuration.rebasePc, Configuration.resumeAt,
          List.map_cons, List.cons_append] using h
    have r₂ : RunsFor program (start.rebasePc first.length) (isolated.resumeAt writeEntry) v₂ := by
      rw [second_layout]
      exact embedded₂
    obtain ⟨actualIsolated, actualRun₂, hIsolated⟩ := r₂.exists_equivalent hCall
    let writer := writeDelimitedContextStart (none :: before) [] (Tape.ofBits (frame reply)).right
      generator (columns.length+1)
    obtain ⟨written, u₃, run₃, hHalt₃, hBits₃⟩ :=
      ChooseDefaultOutput.runs_generator before (Tape.ofBits (frame reply)).right generator (columns.length+1)
    obtain ⟨v₃, _, embedded₃⟩ := run₃.withSubroutine_halted
      (first ++ second) ChooseDefaultOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt₃
    have hWriterCall : (writer.rebasePc (first ++ second).length).Equivalent actualIsolated := by
      refine ⟨?_, ?_, hReady₂.2.2.1.symm.trans hIsolated.2.2.1,
        hReady₂.2.2.2.symm.trans hIsolated.2.2.2⟩
      · rw [← hIsolated.1]
        simp [writer, writeDelimitedContextStart_layout, first, second, writeEntry, isolationEntry,
          Program.asSubroutine_length, Configuration.rebasePc, Configuration.resumeAt, Nat.add_assoc]
      · exact hIsolated.2.1
    have r₃ : RunsFor program (writer.rebasePc (first ++ second).length)
        (written.resumeAt finalPc) v₃ := by rw [third_layout]; exact embedded₃
    obtain ⟨actualWritten, actualRun₃, hWritten⟩ := r₃.exists_equivalent hWriterCall
    have hPc : actualWritten.pc = finalPc := by simpa [Configuration.resumeAt] using hWritten.1.symm
    have hActive : actualWritten.halted = false := hWritten.2.1.symm
    refine ⟨{ actualWritten with halted := true }, v₁+v₂+v₃+1,
      ((r₁.trans actualRun₂).trans actualRun₃).succ (final_step _ hPc hActive), rfl, ?_⟩
    exact hWritten.2.2.2.symm.bits.trans hBits₃

/-- The complete framed fallback terminates on every finite raw request.
In particular, malformed security/instance headers and arbitrary response
bits do not acquire a well-formedness assumption in the time bound. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 10000000000000*(raw.length+1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨prepared, u₁, _, _, hu₁, run₁, hHalt₁, _, _⟩ :=
    FramedExponentPreparation.runs_any_suffix raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedExponentPreparation.program
    (second ++ ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) isolationEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt isolationEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨isolated, u₂, hu₂, run₂, hHalt₂⟩ :=
    InstanceGeneratorIsolation.runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted first InstanceGeneratorIsolation.program
    (ChooseDefaultOutput.program.asSubroutine writeEntry finalPc ++ [.halt]) writeEntry
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt isolationEntry) (isolated.resumeAt writeEntry) v₂ := by
    rw [second_layout]
    simpa [first, isolationEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  obtain ⟨written, u₃, hu₃, run₃, hHalt₃⟩ :=
    ChooseDefaultOutput.runs_tapes isolated.inputTape isolated.outputTape
  obtain ⟨v₃, hv₃, embedded₃⟩ := run₃.withSubroutine_halted (first ++ second)
    ChooseDefaultOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt₃
  have r₃ : RunsFor program (isolated.resumeAt writeEntry) (written.resumeAt finalPc) v₃ := by
    rw [third_layout]
    simpa [first, second, isolationEntry, writeEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt, Nat.add_assoc] using embedded₃
  refine ⟨{ written.resumeAt finalPc with halted := true }, v₁+v₂+v₃+1, ?_,
    ((r₁.trans r₂).trans r₃).succ (final_step _ rfl rfl), rfl⟩
  have hs₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have hs₂ := GuardedCompiler.sourceStorage_le_of_run run₂
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length+2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  simp only [GuardedCompiler.sourceStorage] at hs₁ hs₂ hInitial
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (10000000000000*(raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 10000000000000*(m+1), (PolynomiallyBounded.const 10000000000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- Evaluator correctness under the same polynomial budget used for every
raw input. The arbitrary rejected response contributes no state bits. -/
theorem eval_valid (n : Nat) (modulus exponent generator reply : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ exponent ++ generator) ++ frame reply
    evalWithin program raw (10000000000000*(raw.length+1)) =
      PMF.pure (some (canonicalMessageBits generator generator [])) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus ++ exponent ++ generator) ++ frame reply
  obtain ⟨target, used, run, hHalt, hBits⟩ := runs_valid n modulus exponent generator reply
    hModulus hExponent hGenerator
  have hHalts : HaltsWith program raw (canonicalMessageBits generator generator []) used :=
    ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program raw (10000000000000*(raw.length+1)) used
    (haltsWithin raw) (hHalts.haltsWithin_of_no_randomBit no_randomBit)]
  exact hHalts.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.FramedChooseDefaultOutput
