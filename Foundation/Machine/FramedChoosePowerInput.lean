import Foundation.Machine.FramedChoosePowerColumns
import Foundation.Machine.ChoosePowerResponseEntry

set_option maxRecDepth 8192

namespace Machine.FramedChoosePowerInput

private def firstReturn : Nat := FramedChoosePowerColumns.program.length + 1
private def finalReturn : Nat := firstReturn + ChoosePowerResponseEntry.program.length + 1
private def first : Program := FramedChoosePowerColumns.program.asSubroutine 0 firstReturn

/-- The complete native request prefix for a candidate-power check. It
reads the real encoded instance and response headers, retaining every byte
on the input tape, and positions the arithmetic columns and first candidate.
This stage does not replace the separate tag/width/range acceptance guards. -/
def program : Program := Program.withSubroutine first ChoosePowerResponseEntry.program [.halt] finalReturn

private theorem first_layout : program =
    Program.withSubroutine [] FramedChoosePowerColumns.program
      (ChoosePowerResponseEntry.program.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, first, Program.withSubroutine, firstReturn, Program.asSubroutine_length]

private theorem final_step (c : Configuration) (hPc : c.pc = finalReturn)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    have hIndex : finalReturn = first.length + ChoosePowerResponseEntry.program.length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- On a choose response, the first candidate copier can receive these
actual physical tapes. No decoded bitstring is loaded as an intermediate
machine action; tape equivalence only ignores outer blank padding. -/
theorem runs_valid (n : Nat) (modulus exponent generator body : List Bool)
    (hModulus : modulus.length = n + 3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let reply := false :: body
    let instanceBits := modulus ++ exponent ++ generator
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots
      (List.replicate modulus.length false) exponent modulus
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
    ∃ target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent generator +
        4 * columns.length + 6 * modulus.length + 3 * reply.length + 21 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { Tape.ofBits body with left := before } ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let reply := false :: body
  let instanceBits := modulus ++ exponent ++ generator
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let columns := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
  let saved := generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++
      some false :: List.replicate n (some true)
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedChoosePowerColumns.runs_valid n modulus exponent generator reply hModulus hExponent hGenerator
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedChoosePowerColumns.program
    (ChoosePowerResponseEntry.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, raw] using embedded₁
  obtain ⟨entered, u₂, hu₂, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    ChoosePowerResponseEntry.runs_choose saved columns body
  let canonical : Configuration :=
    { inputTape := { Tape.ofBits (frame reply) with left := saved },
      outputTape := { left := columns.reverse.map some } }
  change RunsFor ChoosePowerResponseEntry.program canonical entered u₂ at run₂
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first ChoosePowerResponseEntry.program [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have hCall : (canonical.rebasePc first.length).Equivalent (prepared.resumeAt firstReturn) := by
    refine ⟨?_, rfl, hInput₁.symm, hOutput₁.symm⟩
    simp [canonical, first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt]
  have r₂ : RunsFor program (canonical.rebasePc first.length) (entered.resumeAt finalReturn) v₂ := embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalReturn := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁ + v₂ + 1, ?_,
    (r₁.trans actualRun₂).succ (final_step actual hPc hActive), rfl, ?_, ?_⟩
  · dsimp only [columns] at hu₂
    omega
  · simpa [saved, instanceBits, reply, List.append_assoc] using hActual.2.2.1.symm.trans hInput₂
  · exact hActual.2.2.2.symm.trans hOutput₂

/-- All arbitrary finite requests stop under a polynomial bound for the
same prefix code. This bound does not assume the request describes an
actual prime-order instance or a canonical choose response. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 1000000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁⟩ := FramedChoosePowerColumns.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedChoosePowerColumns.program
    (ChoosePowerResponseEntry.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨entered, u₂, hu₂, run₂, hHalt₂⟩ := ChoosePowerResponseEntry.runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first ChoosePowerResponseEntry.program [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt firstReturn) (entered.resumeAt finalReturn) v₂ := by
    simpa [program, first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  refine ⟨{ entered.resumeAt finalReturn with halted := true }, v₁ + v₂ + 1,
    ?_, (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  simp only [GuardedCompiler.sourceStorage] at hStorage hInitial
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

/-- The physically prepared canonical tapes are reached under the same
linear bound as the all-input parser. Determinism identifies the bounded
native run; this theorem does not install a mathematical tape value. -/
theorem runs_valid_bounded (n : Nat) (modulus exponent generator body : List Bool)
    (hModulus : modulus.length = n + 3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let reply := false :: body
    let instanceBits := modulus ++ exponent ++ generator
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots
      (List.replicate modulus.length false) exponent modulus
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
    ∃ target used,
      used ≤ 1000000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { Tape.ofBits body with left := before } ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  obtain ⟨canonical, steps, _, run, hHalt, hInput, hOutput⟩ := runs_valid n modulus exponent generator body hModulus hExponent hGenerator
  obtain ⟨target, used, hUsed, bounded, hTargetHalt⟩ := runs_any _
  have hSame := run.halted_finish_eq_of_no_randomBit bounded hHalt hTargetHalt no_randomBit
  subst target
  exact ⟨canonical, used, hUsed, bounded, hHalt, hInput, hOutput⟩

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (1000000000 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 1000000000 * (m + 1), (PolynomiallyBounded.const 1000000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.FramedChoosePowerInput
