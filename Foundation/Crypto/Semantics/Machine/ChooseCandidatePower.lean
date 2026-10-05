import Foundation.Crypto.Semantics.Machine.ChooseCandidatePowerPreparation
import Foundation.Crypto.Semantics.Machine.BinaryPowerIsOne

namespace Machine.ChooseCandidatePower

private def callEntry : Nat := ChooseCandidatePowerPreparation.program.length + 1
private def finalPc (core : Program) : Nat :=
  callEntry + (GuardedCompiler.rawCompileOpposite core).length + 1
private def pre : Program :=
  ChooseCandidatePowerPreparation.program.asSubroutine 0 callEntry

/-- Prepare the three arithmetic tracks and invoke the actual guarded power
code on those same physical tapes. The response remains saved on the input
tape; no whole-string arithmetic or tape reload is a machine instruction. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine pre (GuardedCompiler.rawCompileOpposite core) [.halt] (finalPc core)

def program : Program := withCore BinaryPowerIsOne.program

theorem withCore_no_randomBit (core : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ core) (tape : TapeId) :
    Instruction.randomBit tape ∉ withCore core := by
  have h₁ := Program.asSubroutine_no_randomBit ChooseCandidatePowerPreparation.program
    ChooseCandidatePowerPreparation.no_randomBit 0 callEntry tape
  have h₂ := Program.asSubroutine_no_randomBit (GuardedCompiler.rawCompileOpposite core)
    (GuardedCompiler.rawCompileOpposite_no_randomBit core h) pre.length (finalPc core) tape
  simpa only [withCore, pre, Program.withSubroutine, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro h₁ h₂)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  withCore_no_randomBit BinaryPowerIsOne.program BinaryPowerIsOne.no_randomBit tape


private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] ChooseCandidatePowerPreparation.program
      ((GuardedCompiler.rawCompileOpposite core).asSubroutine callEntry (finalPc core) ++
        [.halt]) callEntry := by
  simp [withCore, pre, callEntry, Program.withSubroutine,
    Program.asSubroutine_length]

private theorem final_step (core : Program) (actual : Configuration)
    (hPc : actual.pc = finalPc core) (hActive : actual.halted = false) :
    Step (withCore core) actual { actual with halted := true } := by
  have hLookup : (withCore core)[finalPc core]? = some .halt := by
    have hIndex : finalPc core = pre.length +
        (GuardedCompiler.rawCompileOpposite core).length + 1 + 0 := by
      simp [finalPc, pre, callEntry, Program.asSubroutine_length]
    change (Program.withSubroutine pre (GuardedCompiler.rawCompileOpposite core) [.halt]
      (finalPc core))[finalPc core]? = some .halt
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The physical candidate copier feeds the guarded call. The returned
configuration identifies the real saved response and arithmetic scratch,
including the blank padding left by output extraction. -/
theorem runs_field_withCore (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (before : List (Option Bool)) (old candidate exponent modulus tail result : List Bool)
    (hOld : old.length = modulus.length)
    (hCandidate : candidate.length = modulus.length)
    (hExponent : exponent.length = modulus.length)
    (halts : HaltsWithin core (BinaryColumnSlotFill.fullSlots candidate exponent modulus)
      (q (BinaryColumnSlotFill.fullSlots candidate exponent modulus).length))
    (correct : evalWithin core (BinaryColumnSlotFill.fullSlots candidate exponent modulus)
      (q (BinaryColumnSlotFill.fullSlots candidate exponent modulus).length) =
        PMF.pure (some result)) :
    let raw := BinaryColumnSlotFill.fullSlots candidate exponent modulus
    let saved := none :: (false :: tail).reverse.map some ++
      (DelimitedTapeComparison.marked candidate).reverse.map some ++ before
    ∃ c target used,
      used ≤ 10 * candidate.length + 2 + 3 * (false :: tail).length + 3 +
        2 * raw.length + 4 + 1 + GuardedCompiler.rawTraceBudget q raw.length + 1 ∧
      RunsFor (withCore core)
        (DelimitedColumnSlotFill.entry
          { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
          (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus))) target used ∧
      target.halted = true ∧ c.halted = true ∧ c.outputBits = result ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom core raw [none] saved c).swapTapes.resumeAt
            (finalPc core) with halted := true } : Configuration) := by
  dsimp only
  let raw := BinaryColumnSlotFill.fullSlots candidate exponent modulus
  let saved := none :: (false :: tail).reverse.map some ++
    (DelimitedTapeComparison.marked candidate).reverse.map some ++ before
  obtain ⟨prepared, u, hu, prepareRun, hPrepareHalt, hInput, hOutput⟩ :=
    ChooseCandidatePowerPreparation.runs_field before old candidate exponent modulus tail
      hOld hCandidate hExponent
  obtain ⟨u', hu', embedded⟩ := prepareRun.withSubroutine_halted
    [] ChooseCandidatePowerPreparation.program
    ((GuardedCompiler.rawCompileOpposite core).asSubroutine callEntry (finalPc core) ++ [.halt])
    callEntry (Nat.zero_le _) rfl hPrepareHalt
  have r₁ : RunsFor (withCore core)
      (DelimitedColumnSlotFill.entry
        { Tape.ofBits (FiniteBitEncoding.delimit candidate ++ tail) with left := before }
        (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (prepared.resumeAt callEntry) u' := by
    simpa only [← first_layout, Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded
  let canonical := (GuardedCompiler.packInputStart [none] saved raw).swapTapes
  have hBoundary : ({ Tape.ofBits raw with left := [none] } : Tape).Equivalent
      (Tape.ofBits raw) := by
    refine ⟨rfl, ?_, fun _ => rfl⟩
    intro i
    cases raw <;> cases i <;> simp [Tape.ofBits]
  have hLayout : (canonical.rebasePc pre.length).Equivalent (prepared.resumeAt callEntry) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [canonical, GuardedCompiler.packInputStart, Configuration.swapTapes,
        Configuration.rebasePc, Configuration.resumeAt, pre,
        Program.asSubroutine_length, callEntry]
    · change ({ left := saved } : Tape).Equivalent prepared.inputTape
      rw [hInput]
      exact Tape.Equivalent.refl _
    · change ({ Tape.ofBits raw with left := [none] } : Tape).Equivalent prepared.outputTape
      exact hBoundary.trans hOutput.symm
  obtain ⟨c, hCoreHalt, hCoreBits, hEval⟩ :=
    GuardedCompiler.rawCompileOpposite_result core raw result [none] saved q
      hNoRandom halts correct
  let returned := (GuardedCompiler.rawResultFrom core raw [none] saved c).swapTapes
  obtain ⟨actual, v, hv, r₂, hReturned⟩ := nativeCall_of_eval
    pre (GuardedCompiler.rawCompileOpposite core) [.halt] (finalPc core)
    canonical returned (prepared.resumeAt callEntry)
    (GuardedCompiler.rawTraceBudget q raw.length)
    (Nat.zero_le _) rfl rfl hEval hLayout
  have hPc : actual.pc = finalPc core := by
    simpa [Configuration.resumeAt] using hReturned.1.symm
  have hActive : actual.halted = false := hReturned.2.1.symm
  refine ⟨c, { actual with halted := true }, u' + v + 1,
    by dsimp only [raw] at hv; omega,
    (r₁.trans r₂).succ (final_step core actual hPc hActive),
    rfl, hCoreHalt, hCoreBits, ?_⟩
  exact ⟨hReturned.1.symm, rfl, hReturned.2.2.1.symm, hReturned.2.2.2.symm⟩

/-- The prepared candidate is tested for `candidate ^ exponent % modulus = 1`
by the finite modular-power and one-bit-checking code. This statement includes
the actual physical input preparation and guarded invocation. -/
theorem runs_numbers (width modulus candidate exponent : Nat)
    (hOne : 1 < modulus) (hCandidate : candidate < modulus)
    (hExponent : exponent < 2 ^ width) (hModulus : modulus < 2 ^ width)
    (before : List (Option Bool)) (tail : List Bool) :
    let candidateBits := Binary.encode width candidate
    let exponentBits := Binary.encode width exponent
    let modulusBits := Binary.encode width modulus
    let raw := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    let saved := none :: (false :: tail).reverse.map some ++
      (DelimitedTapeComparison.marked candidateBits).reverse.map some ++ before
    ∃ c target used,
      used ≤ 10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
        2 * raw.length + 4 + 1 +
          GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget raw.length + 1 ∧
      RunsFor program
        (DelimitedColumnSlotFill.entry
          { Tape.ofBits (FiniteBitEncoding.delimit candidateBits ++ tail) with left := before }
          (Tape.ofBits (BinaryColumnSlotFill.fullSlots
            (List.replicate width false) exponentBits modulusBits))) target used ∧
      target.halted = true ∧ c.halted = true ∧
      c.outputBits = [BinaryIsOneInPlace.accepts
        (Binary.encode width (candidate ^ exponent % modulus))] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom BinaryPowerIsOne.program raw [none] saved c).swapTapes.resumeAt
            (finalPc BinaryPowerIsOne.program) with halted := true } : Configuration) := by
  dsimp only
  exact runs_field_withCore BinaryPowerIsOne.program BinaryPowerIsOne.budget
    BinaryPowerIsOne.no_randomBit before (List.replicate width false)
    (Binary.encode width candidate) (Binary.encode width exponent) (Binary.encode width modulus)
    tail [BinaryIsOneInPlace.accepts (Binary.encode width (candidate ^ exponent % modulus))]
    (by simp) (by simp) (by simp)
    (BinaryPowerIsOne.haltsWithin _)
    (BinaryPowerIsOne.eval_numbers width modulus candidate exponent
      hOne hCandidate hExponent hModulus)

end Machine.ChooseCandidatePower
