import Foundation.Crypto.Semantics.Machine.ChooseRequestPreparation
import Foundation.Crypto.Semantics.Machine.ChooseRangeDecision
import Foundation.Crypto.Semantics.Machine.ChooseWidthDecision

namespace Machine.ChooseSavedCheck

private def callEntry : Nat := ChooseRequestPreparation.program.length + 1
private def finalPc (core : Program) : Nat :=
  callEntry + (GuardedCompiler.rawCompileOpposite core).length + 1
private def pre : Program :=
  ChooseRequestPreparation.program.asSubroutine 0 callEntry

/-- Preserve the entire raw request, then invoke a check through the
opposite-tape guarded interpreter. Its one-bit status can be dispatched
without discarding the original response and arbitrary state suffix. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine pre (GuardedCompiler.rawCompileOpposite core) [.halt] (finalPc core)

def program : Program := withCore ChooseRangeDecision.program

private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] ChooseRequestPreparation.program
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

/-- Operational correctness of the saved-request call, with the actual
protected input and returned guarded scratch identified. The called code
and its certified resource budget remain explicit. -/
theorem runs_request_withCore (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (raw result : List Bool)
    (halts : HaltsWithin core raw (q raw.length))
    (correct : evalWithin core raw (q raw.length) = PMF.pure (some result)) :
    let saved := none :: raw.reverse.map some
    ∃ c target used,
      used ≤ 8 * raw.length + 10 + GuardedCompiler.rawTraceBudget q raw.length + 1 ∧
      RunsFor (withCore core) (Configuration.initial raw) target used ∧
      target.halted = true ∧ c.halted = true ∧ c.outputBits = result ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom core raw [none] saved c).swapTapes.resumeAt
            (finalPc core) with halted := true } : Configuration) := by
  dsimp only
  let saved := none :: raw.reverse.map some
  obtain ⟨prepared, u, hu, prepareRun, hPrepareHalt, hInput, hOutput⟩ :=
    ChooseRequestPreparation.runs_request raw
  obtain ⟨u', hu', embedded⟩ := prepareRun.withSubroutine_halted
    [] ChooseRequestPreparation.program
    ((GuardedCompiler.rawCompileOpposite core).asSubroutine callEntry (finalPc core) ++ [.halt])
    callEntry (Nat.zero_le _) rfl hPrepareHalt
  have r₁ : RunsFor (withCore core) (Configuration.initial raw)
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
    by omega,
    (r₁.trans r₂).succ (final_step core actual hPc hActive),
    rfl, hCoreHalt, hCoreBits, ?_⟩
  exact ⟨hReturned.1.symm, rfl, hReturned.2.2.1.symm, hReturned.2.2.2.symm⟩

/-- The range check operates on the copied real request. Its return value
identifies the original request saved for the next native dispatch/reset. -/
theorem runs_ranges (n width : Nat) (modulus suffix first second tail : List Bool)
    (hWidth : 0 < width) (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    let status := decide (Binary.value first < Binary.value modulus ∧
      Binary.value second < Binary.value modulus)
    ∃ c target used,
      used ≤ 8 * raw.length + 10 +
        GuardedCompiler.rawTraceBudget ChooseRangeDecision.budget raw.length + 1 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ c.halted = true ∧ c.outputBits = [status] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom ChooseRangeDecision.program raw [none]
              (none :: raw.reverse.map some) c).swapTapes.resumeAt
            (finalPc ChooseRangeDecision.program) with halted := true } : Configuration) := by
  dsimp only
  exact runs_request_withCore ChooseRangeDecision.program ChooseRangeDecision.budget
    ChooseRangeDecision.no_randomBit _ _ (ChooseRangeDecision.haltsWithin _)
    (ChooseRangeDecision.eval_decisions n width modulus suffix first second tail
      hWidth hModulus hInstance hFirst hSecond)

/-- Preserve the whole original request while checking arbitrary raw
choose fields. The guarded result has exactly one status bit, so the saved
request can feed the existing native dispatch and reset continuations. -/
theorem runs_widths (n width : Nat) (instanceBits payload : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: payload)
    let status := (FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = width) &&
        (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))
    ∃ c target used,
      used ≤ 8 * raw.length + 10 +
        GuardedCompiler.rawTraceBudget ChooseWidthDecision.budget raw.length + 1 ∧
      RunsFor (withCore ChooseWidthDecision.program) (Configuration.initial raw) target used ∧
      target.halted = true ∧ c.halted = true ∧ c.outputBits = [status] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom ChooseWidthDecision.program raw [none]
              (none :: raw.reverse.map some) c).swapTapes.resumeAt
            (finalPc ChooseWidthDecision.program) with halted := true } : Configuration) := by
  dsimp only
  exact runs_request_withCore ChooseWidthDecision.program ChooseWidthDecision.budget
    ChooseWidthDecision.no_randomBit _ _ (ChooseWidthDecision.haltsWithin _)
    (ChooseWidthDecision.eval_raw_decision n width instanceBits payload hLength)

/-- Empty or wrong-stage responses produce the same one-bit rejection
while the entire framed request is protected for the fallback continuation. -/
theorem runs_widths_wrong_tag (n : Nat) (instanceBits reply : List Bool)
    (hTag : (Tape.ofBits reply).current = none ∨ (Tape.ofBits reply).current = some true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ c target used,
      used ≤ 8 * raw.length + 10 +
        GuardedCompiler.rawTraceBudget ChooseWidthDecision.budget raw.length + 1 ∧
      RunsFor (withCore ChooseWidthDecision.program) (Configuration.initial raw) target used ∧
      target.halted = true ∧ c.halted = true ∧ c.outputBits = [false] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom ChooseWidthDecision.program raw [none]
              (none :: raw.reverse.map some) c).swapTapes.resumeAt
            (finalPc ChooseWidthDecision.program) with halted := true } : Configuration) := by
  dsimp only
  exact runs_request_withCore ChooseWidthDecision.program ChooseWidthDecision.budget
    ChooseWidthDecision.no_randomBit _ _ (ChooseWidthDecision.haltsWithin _)
    (ChooseWidthDecision.eval_wrong_tag n instanceBits reply hTag)

/-- Finite storage and malformed request headers do not affect termination:
the copied request is supplied to the same certified guarded interpreter. -/
theorem runs_request_terminating (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (raw : List Bool) (halts : HaltsWithin core raw (q raw.length)) :
    ∃ target used,
      used ≤ 8 * raw.length + 10 + GuardedCompiler.rawTraceBudget q raw.length + 1 ∧
      RunsFor (withCore core) (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨source, u, hu, sourceRun, sourceHalt⟩ :=
    exists_halted_run_of_haltsFrom core (Configuration.initial raw) (q raw.length) halts
  have sourceCorrect : evalWithin core raw (q raw.length) = PMF.pure (some source.outputBits) := by
    have hWith : HaltsWith core raw source.outputBits u :=
      ⟨source, sourceRun, sourceHalt, rfl⟩
    rw [evalWithin_eq_of_haltsWithin core raw (q raw.length) u halts
      (hWith.haltsWithin_of_no_randomBit hNoRandom)]
    exact hWith.evalWithin_eq_pure_of_no_randomBit hNoRandom
  obtain ⟨c, target, used, hUsed, run, hHalt, _, _, _⟩ :=
    runs_request_withCore core q hNoRandom raw source.outputBits halts sourceCorrect
  exact ⟨target, used, hUsed, run, hHalt⟩

theorem withCore_no_randomBit (core : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ core) (tape : TapeId) :
    Instruction.randomBit tape ∉ withCore core := by
  have h₁ := Program.asSubroutine_no_randomBit ChooseRequestPreparation.program
    ChooseRequestPreparation.no_randomBit 0 callEntry tape
  have h₂ := Program.asSubroutine_no_randomBit (GuardedCompiler.rawCompileOpposite core)
    (GuardedCompiler.rawCompileOpposite_no_randomBit core h) pre.length (finalPc core) tape
  simpa only [withCore, pre, Program.withSubroutine, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro h₁ h₂)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

def budget (q : Nat → Nat) (length : Nat) : Nat :=
  8 * length + 10 + GuardedCompiler.rawTraceBudget q length + 1

theorem haltsWithin_withCore (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (hHalts : ∀ raw, HaltsWithin core raw (q raw.length)) (raw : List Bool) :
    HaltsWithin (withCore core) raw (budget q raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ :=
    runs_request_terminating core q hNoRandom raw (hHalts raw)
  exact run.haltsFrom_of_no_randomBit hHalt (withCore_no_randomBit core hNoRandom) hUsed

theorem budget_polynomial {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (budget q) :=
  (((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 10)).add
      (GuardedCompiler.rawTraceBudget_polynomiallyBounded hq) |>.add
        (PolynomiallyBounded.const 1)

/-- In particular the saved-request numeric-range call halts on every raw
input. Correctness of its range predicate still uses complete field widths. -/
theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget ChooseRangeDecision.budget raw.length) :=
  haltsWithin_withCore ChooseRangeDecision.program ChooseRangeDecision.budget
    ChooseRangeDecision.no_randomBit ChooseRangeDecision.haltsWithin raw

theorem polynomialTime : PolynomialTime program :=
  ⟨budget ChooseRangeDecision.budget,
    budget_polynomial ChooseRangeDecision.budget_polynomial, haltsWithin⟩

/-- Saving a request and checking its widths retains the all-input
polynomial stopping guarantee of the native width decision. -/
theorem widths_polynomialTime : PolynomialTime (withCore ChooseWidthDecision.program) :=
  ⟨budget ChooseWidthDecision.budget,
    budget_polynomial ChooseWidthDecision.budget_polynomial,
    haltsWithin_withCore ChooseWidthDecision.program ChooseWidthDecision.budget
      ChooseWidthDecision.no_randomBit ChooseWidthDecision.haltsWithin⟩

end Machine.ChooseSavedCheck
