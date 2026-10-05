import Foundation.Crypto.Semantics.Machine.ChooseRangeValidation
import Foundation.Crypto.Semantics.Machine.ChooseDecisionOutput

set_option maxRecDepth 4096

namespace Machine.ChooseRangeDecision

private def backEntry : Nat := ChooseRangeValidation.program.length+1
private def decisionEntry : Nat := backEntry+1
private def finalPc : Nat := decisionEntry+ChooseDecisionOutput.program.length+1
private def beforeDecision : Program :=
  ChooseRangeValidation.program.asSubroutine 0 backEntry ++ [.moveLeft .output]

/-- The range checks, their real status read, workspace erasure, and
one-bit result are one finite program. A caller can use this as a guarded
check while separately preserving its original request. This program tests
numeric range only; it does not test subgroup membership or element width. -/
def program : Program := Program.withSubroutine beforeDecision ChooseDecisionOutput.program [.halt] finalPc

private theorem first_layout : program =
    Program.withSubroutine [] ChooseRangeValidation.program
      ([.moveLeft .output] ++ ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) backEntry := by
  simp [program, beforeDecision, Program.withSubroutine, decisionEntry, backEntry,
    Program.asSubroutine_length, List.append_assoc]

private theorem back_step (c : Configuration) (hPc : c.pc = backEntry)
    (hActive : c.halted = false) :
    Step program c { c with pc := decisionEntry, outputTape := c.outputTape.moveLeft } := by
  have hLookup : program[backEntry]? = some (.moveLeft .output) := by
    rw [first_layout]
    have hIndex : backEntry = [].length+ChooseRangeValidation.program.length+1+0 := rfl
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next,
    Configuration.advance, Configuration.updateTape, decisionEntry]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = beforeDecision.length+ChooseDecisionOutput.program.length+1+0 := by
      simp [finalPc, beforeDecision, decisionEntry, backEntry, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

private theorem decision_layout (modulus suffix : List Bool) (status : Bool)
    (hSuffix : suffix ≠ []) :
    ({ Tape.ofBits (status :: (modulus ++ suffix)) with left := [none] } : Tape).Equivalent
      ((({ current := some status,
           right := modulus.map some ++ (Tape.ofBits suffix).current :: (Tape.ofBits suffix).right } : Tape).moveRight).moveLeft) := by
  cases hS : suffix with
  | nil => exact False.elim (hSuffix hS)
  | cons bit rest =>
      cases modulus with
      | nil => exact ⟨rfl, by intro i; cases i <;> rfl, fun _ => rfl⟩
      | cons first remaining =>
          refine ⟨rfl, ?_, ?_⟩
          · intro i; cases i <;> rfl
          · intro i
            simp [Tape.ofBits, Tape.moveRight, Tape.moveLeft, List.map_append]

/-- For positive represented width and two complete fields, the result
is precisely their numeric-range conjunction. The state suffix is arbitrary.
Workspace cleanup and the decision write belong to this same actual run. -/
theorem runs_decisions (n width : Nat) (modulus suffix first second tail : List Bool)
    (hWidth : 0 < width) (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3*width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.outputBits = [decide (Binary.value first < Binary.value modulus ∧
        Binary.value second < Binary.value modulus)] := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
  let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
  let status := decide (Binary.value first < Binary.value modulus ∧ Binary.value second < Binary.value modulus)
  obtain ⟨checked, u₁, run₁, hHalt₁, _, _, hOutput₁⟩ :=
    ChooseRangeValidation.runs_matching_layout n width modulus suffix first second tail
      hModulus hInstance hFirst hSecond
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted [] ChooseRangeValidation.program
    ([.moveLeft .output] ++ ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) backEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt backEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  let backed : Configuration :=
    { checked.resumeAt backEntry with pc := decisionEntry, outputTape := checked.outputTape.moveLeft }
  have rBack : RunsFor program (checked.resumeAt backEntry) backed 1 :=
    (RunsFor.zero _).succ (back_step _ rfl rfl)
  have hSuffix : suffix ≠ [] := by
    intro h
    simp only [List.length_append, h, List.length_nil, Nat.add_zero, hModulus] at hInstance
    omega
  obtain ⟨written, u₂, run₂, hHalt₂, _, hBits₂⟩ :=
    ChooseDecisionOutput.runs_bits [] (modulus ++ suffix) status checked.inputTape
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted beforeDecision ChooseDecisionOutput.program [.halt]
    finalPc (Nat.zero_le _) rfl hHalt₂
  let source : Configuration :=
    { inputTape := checked.inputTape,
      outputTape := { Tape.ofBits (status :: (modulus ++ suffix)) with left := [none] } }
  have hCall : (source.rebasePc beforeDecision.length).Equivalent backed := by
    refine ⟨?_, rfl, Tape.Equivalent.refl _, ?_⟩
    · simp [source, beforeDecision, decisionEntry, backEntry, Program.asSubroutine_length,
        backed, Configuration.rebasePc, Configuration.resumeAt]
    · exact (decision_layout modulus suffix status hSuffix).trans hOutput₁.symm.moveLeft
  have r₂ : RunsFor program (source.rebasePc beforeDecision.length) (written.resumeAt finalPc) v₂ := by
    unfold program
    exact embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalPc := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁+1+v₂+1,
    ((r₁.trans rBack).trans actualRun₂).succ (final_step _ hPc hActive), rfl, ?_⟩
  exact hActual.2.2.2.symm.bits.trans hBits₂

def budget (length : Nat) : Nat := 1000*(ChooseRangeValidation.budget length+length+10)

/-- All finite raw inputs terminate, without relying on positive width or
well-formed parameters. Those premises occur only in the correctness result. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨checked, u₁, hu₁, run₁, hHalt₁⟩ := ChooseRangeValidation.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted [] ChooseRangeValidation.program
    ([.moveLeft .output] ++ ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) backEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt backEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  let backed : Configuration :=
    { checked.resumeAt backEntry with pc := decisionEntry, outputTape := checked.outputTape.moveLeft }
  have rBack : RunsFor program (checked.resumeAt backEntry) backed 1 :=
    (RunsFor.zero _).succ (back_step _ rfl rfl)
  obtain ⟨written, u₂, hu₂, run₂, hHalt₂, _⟩ := ChooseDecisionOutput.runs_any backed.inputTape backed.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted beforeDecision ChooseDecisionOutput.program [.halt]
    finalPc (Nat.zero_le _) rfl hHalt₂
  have hEntry : ({ inputTape := backed.inputTape, outputTape := backed.outputTape } : Configuration).rebasePc
      beforeDecision.length = backed := by
    simp [beforeDecision, decisionEntry, backEntry, Program.asSubroutine_length,
      backed, Configuration.rebasePc, Configuration.resumeAt]
  have r₂ : RunsFor program backed (written.resumeAt finalPc) v₂ := by
    unfold program
    simpa only [hEntry] using embedded₂
  refine ⟨{ written.resumeAt finalPc with halted := true }, v₁+1+v₂+1, ?_,
    ((r₁.trans rBack).trans r₂).succ (final_step _ rfl rfl), rfl⟩
  have hs₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have hsBack := GuardedCompiler.sourceStorage_le_of_run rBack
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length+2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hs₁ hsBack hInitial
  dsimp only [budget]
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem budget_polynomial : PolynomiallyBounded budget := by
  unfold budget
  exact (PolynomiallyBounded.const 1000).mul
    ((ChooseRangeValidation.budget_polynomial.add PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 10))

theorem polynomialTime : PolynomialTime program := ⟨budget, budget_polynomial, haltsWithin⟩

/-- The one-bit evaluator result uses the same public all-input polynomial
budget. No copied instance bits remain mixed into the returned decision. -/
theorem eval_decisions (n width : Nat) (modulus suffix first second tail : List Bool)
    (hWidth : 0 < width) (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3*width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    evalWithin program raw (budget raw.length) = PMF.pure (some
      [decide (Binary.value first < Binary.value modulus ∧ Binary.value second < Binary.value modulus)]) := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
  let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
  obtain ⟨target, used, run, hHalt, hBits⟩ := runs_decisions n width modulus suffix first second tail
    hWidth hModulus hInstance hFirst hSecond
  have hHalts : HaltsWith program raw
      [decide (Binary.value first < Binary.value modulus ∧ Binary.value second < Binary.value modulus)] used :=
    ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program raw (budget raw.length) used
    (haltsWithin raw) (hHalts.haltsWithin_of_no_randomBit no_randomBit)]
  exact hHalts.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.ChooseRangeDecision
