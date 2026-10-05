import Foundation.Crypto.Semantics.Machine.FramedExponentPreparation
import Foundation.Crypto.Semantics.Machine.InstanceGeneratorSkip

set_option maxRecDepth 8192

namespace Machine.FramedChoosePowerColumns

private def firstReturn : Nat := FramedExponentPreparation.program.length + 1
private def finalReturn : Nat := firstReturn + InstanceGeneratorSkip.program.length + 1
private def first : Program := FramedExponentPreparation.program.asSubroutine 0 firstReturn

/-- Prepare the exponent and modulus from the actual instance frame and
advance across its generator field. The response frame is still unread;
all bytes consumed on the way remain on the same physical input tape. -/
def program : Program :=
  Program.withSubroutine first InstanceGeneratorSkip.program [.halt] finalReturn

private theorem first_layout : program =
    Program.withSubroutine [] FramedExponentPreparation.program
      (InstanceGeneratorSkip.program.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, first, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) (hPc : c.pc = finalReturn)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    have hIndex : finalReturn = first.length + InstanceGeneratorSkip.program.length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Exact frame-to-columns trace, without decoding and reloading either
tape between the linked native stages. -/
theorem runs_valid (n : Nat) (modulus exponent generator reply : List Bool)
    (hModulus : modulus.length = n + 3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let instanceBits := modulus ++ exponent ++ generator
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots
      (List.replicate modulus.length false) exponent modulus
    let before := generator.reverse.map some ++ exponent.reverse.map some ++
      modulus.reverse.map some ++ some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
    ∃ target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent generator +
        2 * columns.length + 6 * modulus.length + 11 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { Tape.ofBits (frame reply) with left := before } ∧
      target.outputTape.Equivalent { left := columns.reverse.map some } := by
  dsimp only
  let instanceBits := modulus ++ exponent ++ generator
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let columns := BinaryColumnSlotFill.fullSlots
    (List.replicate modulus.length false) exponent modulus
  let saved := modulus.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++
      some false :: List.replicate n (some true)
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent generator (frame reply) hModulus hExponent
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedExponentPreparation.program
    (InstanceGeneratorSkip.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨skipped, u₂, hu₂, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    InstanceGeneratorSkip.runs_generator (List.replicate modulus.length false) exponent modulus
      generator (frame reply) (by simp) hExponent hGenerator
      (exponent.reverse.map some ++ saved)
  let canonical : Configuration :=
    { inputTape := { Tape.ofBits (generator ++ frame reply) with
        left := exponent.reverse.map some ++ saved },
      outputTape := { left := none :: columns.reverse.map some } }
  change RunsFor InstanceGeneratorSkip.program canonical skipped u₂ at run₂
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first InstanceGeneratorSkip.program [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have hCall : (canonical.rebasePc first.length).Equivalent (prepared.resumeAt firstReturn) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [canonical, first, firstReturn, Program.asSubroutine_length,
        Configuration.rebasePc, Configuration.resumeAt]
    · exact hInput₁.symm
    · exact hOutput₁.symm
  have r₂ : RunsFor program (canonical.rebasePc first.length)
      (skipped.resumeAt finalReturn) v₂ := embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalReturn := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁ + v₂ + 1, ?_,
    (r₁.trans actualRun₂).succ (final_step actual hPc hActive), rfl, ?_, ?_⟩
  · omega
  · simpa [saved, instanceBits, List.append_assoc] using hActual.2.2.1.symm.trans hInput₂
  · exact hActual.2.2.2.symm.trans hOutput₂

/-- A malformed instance or reply cannot prevent this same finite code
from stopping. The resource bound uses actual tape storage after the first
stage, rather than a well-formedness assumption. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 4000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨prepared, u₁, remaining, before, hu₁, run₁, hHalt₁, hInput₁, hLength₁⟩ :=
    FramedExponentPreparation.runs_any_suffix raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedExponentPreparation.program
    (InstanceGeneratorSkip.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨skipped, u₂, hu₂, run₂, hHalt₂⟩ :=
    InstanceGeneratorSkip.runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first InstanceGeneratorSkip.program [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt firstReturn) (skipped.resumeAt finalReturn) v₂ := by
    simpa [program, first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  refine ⟨{ skipped.resumeAt finalReturn with halted := true }, v₁ + v₂ + 1,
    ?_, (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  simp only [GuardedCompiler.sourceStorage] at hStorage hInitial
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (4000000 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 4000000 * (m + 1), (PolynomiallyBounded.const 4000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.FramedChoosePowerColumns
