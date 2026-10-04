import Foundation.Machine.FramedChoosePowerInput
import Foundation.Machine.DelimitedSkip

set_option maxRecDepth 8192

namespace Machine.FramedChooseSecondPowerInput

private def firstReturn : Nat := FramedChoosePowerInput.program.length + 1
private def finalReturn : Nat := firstReturn + skipDelimited.length + 1
private def first : Program := FramedChoosePowerInput.program.asSubroutine 0 firstReturn

/-- Prepare the same arithmetic columns from the original request, then
skip the first delimited response field with actual input-head moves.
The second candidate and arbitrary trailing state remain unread. -/
def program : Program := Program.withSubroutine first skipDelimited [.halt] finalReturn

private theorem first_layout : program =
    Program.withSubroutine [] FramedChoosePowerInput.program
      (skipDelimited.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, first, firstReturn, Program.withSubroutine, Program.asSubroutine_length]

private theorem final_step (c : Configuration) (hPc : c.pc = finalReturn)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    have hIndex : finalReturn = first.length + skipDelimited.length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

private theorem start_layout (before : List (Option Bool)) (field tail : List Bool) (output : Tape) :
    skipDelimitedStart before field (tail.map some) output =
      { inputTape := { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with left := before },
        outputTape := output } := by
  rw [skipDelimitedStart_layout]
  cases field <;> simp [FiniteBitEncoding.delimit, List.map_append, Tape.ofBits, Tape.moveRight]

private theorem finish_layout (before : List (Option Bool)) (field tail : List Bool) (output : Tape) :
    (skipDelimitedFinish before field (tail.map some) output).inputTape =
      { Tape.ofBits tail with left := (FiniteBitEncoding.delimit field).reverse.map some ++ before } := by
  rw [skipDelimitedFinish_layout_cells]
  cases tail <;> rfl

/-- Exact physical layout for the second candidate's power call. The first
candidate remains in the saved request prefix; it is not copied into an
arbitrary replacement tape. -/
theorem runs_valid (n : Nat) (modulus exponent generator firstBits tail : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let instanceBits := modulus ++ exponent ++ generator
    let reply := false :: FiniteBitEncoding.delimit firstBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    ∃ target used,
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits tail with left := (FiniteBitEncoding.delimit firstBits).reverse.map some ++ before } ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let instanceBits := modulus ++ exponent ++ generator
  let body := FiniteBitEncoding.delimit firstBits ++ tail
  let reply := false :: body
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let columns := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
  let before := some false :: some false :: List.replicate reply.length (some true) ++
    generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
  obtain ⟨prepared, u₁, _, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedChoosePowerInput.runs_valid n modulus exponent generator body hModulus hExponent hGenerator
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedChoosePowerInput.program (skipDelimited.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial request) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, request, reply] using embedded₁
  have run₂ := skipDelimited_runs before firstBits (tail.map some) (Tape.ofBits columns)
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted
    first skipDelimited [.halt] finalReturn (Nat.zero_le _) rfl rfl
  have hCall : ((skipDelimitedStart before firstBits (tail.map some) (Tape.ofBits columns)).rebasePc
      first.length).Equivalent (prepared.resumeAt firstReturn) := by
    rw [start_layout]
    refine ⟨?_, rfl, hInput₁.symm, hOutput₁.symm⟩
    simp [Configuration.rebasePc, Configuration.resumeAt, first, firstReturn, Program.asSubroutine_length]
  have r₂ : RunsFor program
      ((skipDelimitedStart before firstBits (tail.map some) (Tape.ofBits columns)).rebasePc first.length)
      ((skipDelimitedFinish before firstBits (tail.map some) (Tape.ofBits columns)).resumeAt finalReturn) v₂ :=
    embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalReturn := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁+v₂+1,
    (r₁.trans actualRun₂).succ (final_step actual hPc hActive), rfl, ?_, hActual.2.2.2.symm⟩
  have hEquiv : actual.inputTape.Equivalent
      (skipDelimitedFinish before firstBits (tail.map some) (Tape.ofBits columns)).inputTape := hActual.2.2.1.symm
  rw [finish_layout] at hEquiv
  simpa only [before, instanceBits, reply, body, List.cons_append, List.append_assoc] using hEquiv

theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 10000000000 * (raw.length+1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁⟩ := FramedChoosePowerInput.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedChoosePowerInput.program (skipDelimited.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨skipped, u₂, hu₂, run₂, hHalt₂, _⟩ :=
    skipDelimited_terminates_from_anyTape prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first skipDelimited [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt firstReturn) (skipped.resumeAt finalReturn) v₂ := by
    simpa [program, first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length+2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  refine ⟨{ skipped.resumeAt finalReturn with halted := true }, v₁+v₂+1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  simp only [GuardedCompiler.sourceStorage] at hStorage hInitial
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

/-- The physically prepared canonical tapes are reached under the same
linear bound as the all-input parser. Determinism identifies the bounded
native run; this theorem does not install a mathematical tape value. -/
theorem runs_valid_bounded (n : Nat) (modulus exponent generator firstBits tail : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let instanceBits := modulus ++ exponent ++ generator
    let reply := false :: FiniteBitEncoding.delimit firstBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    ∃ target used, used ≤ 10000000000 * (request.length + 1) ∧
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits tail with left := (FiniteBitEncoding.delimit firstBits).reverse.map some ++ before } ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  obtain ⟨canonical, steps, run, hHalt, hInput, hOutput⟩ := runs_valid n modulus exponent generator firstBits tail hModulus hExponent hGenerator
  obtain ⟨target, used, hUsed, bounded, hTargetHalt⟩ := runs_any _
  have hSame := run.halted_finish_eq_of_no_randomBit bounded hHalt hTargetHalt no_randomBit
  subst target
  exact ⟨canonical, used, hUsed, bounded, hHalt, hInput, hOutput⟩

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (10000000000 * (raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 10000000000 * (m+1), (PolynomiallyBounded.const 10000000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.FramedChooseSecondPowerInput
