import Foundation.Crypto.Semantics.Machine.ChooseTwoWidthsPrefix
import Foundation.Crypto.Semantics.Machine.ChooseDecisionOutput
import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine.ChooseWidthDecision

private def decisionEntry : Nat := ChooseTwoWidthsPrefix.program.length + 1
private def finalPc : Nat := decisionEntry + ChooseDecisionOutput.program.length + 1
private def beforeDecision : Program := ChooseTwoWidthsPrefix.program.asSubroutine 0 decisionEntry

/-- Read the stage tag and both widths, then erase the copied counter and
return the remembered decision bit. The code contains actual width scans,
workspace erasure, and output instructions; it never invokes a decoder. -/
def program : Program :=
  Program.withSubroutine beforeDecision ChooseDecisionOutput.program [.halt] finalPc

private theorem first_layout : program =
    Program.withSubroutine [] ChooseTwoWidthsPrefix.program
      (ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) decisionEntry := by
  simp [program, beforeDecision, Program.withSubroutine, decisionEntry,
    Program.asSubroutine_length, List.append_assoc]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = beforeDecision.length + ChooseDecisionOutput.program.length + 1 + 0 := by
      simp [finalPc, beforeDecision, decisionEntry, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Any certified physical status layout can feed the same native decision
output, including rejection layouts once the width scanner establishes them.
The prefix trace and its retained workspace are operational premises. -/
theorem runs_status (raw beforeBits rest : List Bool) (status : Bool)
    (checked : Configuration) (used : Nat)
    (run : RunsFor ChooseTwoWidthsPrefix.program (Configuration.initial raw) checked used)
    (hHalt : checked.halted = true)
    (hOutput : checked.outputTape.Equivalent
      ({ Tape.ofBits (status :: rest) with left := beforeBits.reverse.map some ++ [none] } : Tape)) :
    ∃ target total,
      RunsFor program (Configuration.initial raw) target total ∧
      target.halted = true ∧ target.outputBits = [status] := by
  obtain ⟨v₁, _, embedded₁⟩ := run.withSubroutine_halted [] ChooseTwoWidthsPrefix.program
    (ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) decisionEntry
    (Nat.zero_le _) rfl hHalt
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt decisionEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨written, u₂, run₂, hHalt₂, _, hBits₂⟩ :=
    ChooseDecisionOutput.runs_bits beforeBits rest status checked.inputTape
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted beforeDecision
    ChooseDecisionOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt₂
  let source : Configuration :=
    { inputTape := checked.inputTape,
      outputTape := { Tape.ofBits (status :: rest) with left := beforeBits.reverse.map some ++ [none] } }
  have hCall : (source.rebasePc beforeDecision.length).Equivalent (checked.resumeAt decisionEntry) := by
    refine ⟨?_, rfl, Tape.Equivalent.refl _, hOutput.symm⟩
    simp [source, beforeDecision, decisionEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt]
  have r₂ : RunsFor program (source.rebasePc beforeDecision.length) (written.resumeAt finalPc) v₂ := by
    unfold program
    exact embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalPc := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁ + v₂ + 1,
    (r₁.trans actualRun₂).succ (final_step _ hPc hActive), rfl, ?_⟩
  exact hActual.2.2.2.symm.bits.trans hBits₂

/-- Every raw choose payload returns exactly one decision bit, even when
one delimiter is missing or either complete field has the wrong width.
The actual retained instance workspace is erased by the native output code. -/
theorem runs_raw_decision (n width : Nat) (instanceBits payload : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: payload
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let decision := (FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = width) &&
        (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))
    ∃ target used, RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits = [decision] := by
  dsimp only
  obtain ⟨checked, used, run, hHalt, hStatus, consumed, suffix, _, hOutput⟩ :=
    ChooseTwoWidthsPrefix.runs_raw_layout n width instanceBits payload hLength
  apply runs_status _ consumed (suffix.drop 1) _ checked used run hHalt
  apply hOutput.trans
  rw [hStatus]
  cases suffix <;> exact Tape.Equivalent.refl _

/-- Two complete matching fields return success without mixing copied
instance bits into the result. The response state remains arbitrary. This
forward result does not yet characterize all malformed response shapes. -/
theorem runs_matching (n width : Nat) (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits = [true] := by
  dsimp only
  obtain ⟨checked, used, run, hHalt, _, hOutput⟩ :=
    ChooseTwoWidthsPrefix.runs_matching_layout n width instanceBits first second tail hLength hFirst hSecond
  apply runs_status _ instanceBits [] true checked used run hHalt
  simpa [DelimitedTripleWidthCheck.finish, Tape.ofBits] using hOutput

/-- Empty and wrong-stage replies take the rejecting native branch. The
counter is physically erased before the sole false bit is returned. No
shape or length assumption on either element field is used here. -/
theorem runs_wrong_tag (n : Nat) (instanceBits reply : List Bool)
    (hTag : (Tape.ofBits reply).current = none ∨ (Tape.ofBits reply).current = some true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits = [false] := by
  dsimp only
  obtain ⟨checked, used, run, hHalt, _, hOutput⟩ :=
    ChooseTwoWidthsPrefix.runs_wrong_tag_layout n instanceBits reply hTag
  apply runs_status _ [] (instanceBits.drop 1) false checked used run hHalt
  have hCounter := (rewindScratchFinish_input_equivalent [] instanceBits checked.inputTape).write (some false)
  change ((({ right := instanceBits.map some ++ [none] } : Tape).moveRight).write (some false)).Equivalent
    (({ Tape.ofBits instanceBits with left := [none] } : Tape).write (some false)) at hCounter
  rw [hOutput]
  apply hCounter.trans
  cases instanceBits with
  | nil =>
      exact ⟨rfl, by intro i; cases i <;> rfl, fun _ => rfl⟩
  | cons bit rest =>
      exact ⟨rfl, by intro i; cases i <;> rfl, fun _ => rfl⟩

def budget (length : Nat) : Nat := 1000 * (ChooseTwoWidthsPrefix.budget length + length + 10)

/-- Every finite raw input, including malformed frames and missing
field delimiters, terminates under the same public polynomial budget. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨checked, u₁, hu₁, run₁, hHalt₁⟩ := ChooseTwoWidthsPrefix.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted [] ChooseTwoWidthsPrefix.program
    (ChooseDecisionOutput.program.asSubroutine decisionEntry finalPc ++ [.halt]) decisionEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt decisionEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨written, u₂, hu₂, run₂, hHalt₂, _⟩ := ChooseDecisionOutput.runs_any checked.inputTape checked.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted beforeDecision
    ChooseDecisionOutput.program [.halt] finalPc (Nat.zero_le _) rfl hHalt₂
  have hEntry : ({ inputTape := checked.inputTape, outputTape := checked.outputTape } : Configuration).rebasePc
      beforeDecision.length = checked.resumeAt decisionEntry := by
    simp [beforeDecision, decisionEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt]
  have r₂ : RunsFor program (checked.resumeAt decisionEntry) (written.resumeAt finalPc) v₂ := by
    unfold program
    simpa only [hEntry] using embedded₂
  refine ⟨{ written.resumeAt finalPc with halted := true }, v₁ + v₂ + 1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  have hs₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  simp only [GuardedCompiler.sourceStorage] at hs₁ hInitial
  dsimp only [budget]
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  have h₁ := Program.asSubroutine_no_randomBit ChooseTwoWidthsPrefix.program
    ChooseTwoWidthsPrefix.no_randomBit 0 decisionEntry tape
  have h₂ := Program.asSubroutine_no_randomBit ChooseDecisionOutput.program
    ChooseDecisionOutput.no_randomBit beforeDecision.length finalPc tape
  simpa only [program, beforeDecision, Program.withSubroutine, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro h₁ h₂)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem budget_polynomial : PolynomiallyBounded budget := by
  have hPrefix : PolynomiallyBounded ChooseTwoWidthsPrefix.budget :=
    ChooseTwoWidthsPrefix.budget_polynomial
  exact (PolynomiallyBounded.const 1000).mul
    ((hPrefix.add PolynomiallyBounded.id).add (PolynomiallyBounded.const 10))

theorem polynomialTime : PolynomialTime program := ⟨budget, budget_polynomial, haltsWithin⟩

/-- The same public polynomial budget evaluates every raw choose payload
according to the two complete-field width tests. -/
theorem eval_raw_decision (n width : Nat) (instanceBits payload : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: payload
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let decision := (FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = width) &&
        (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))
    evalWithin program raw (budget raw.length) = PMF.pure (some [decision]) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    runs_raw_decision n width instanceBits payload hLength
  have hWith : HaltsWith program _ _ used := ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program _ (budget _) used (haltsWithin _)
    (hWith.haltsWithin_of_no_randomBit no_randomBit)]
  exact hWith.evalWithin_eq_pure_of_no_randomBit no_randomBit

theorem eval_matching (n width : Nat) (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    evalWithin program raw (budget raw.length) = PMF.pure (some [true]) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hBits⟩ := runs_matching n width instanceBits first second tail hLength hFirst hSecond
  have hWith : HaltsWith program _ [true] used := ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program _ (budget _) used (haltsWithin _)
    (hWith.haltsWithin_of_no_randomBit no_randomBit)]
  exact hWith.evalWithin_eq_pure_of_no_randomBit no_randomBit

/-- Rejecting evaluator result at the same all-input polynomial budget. -/
theorem eval_wrong_tag (n : Nat) (instanceBits reply : List Bool)
    (hTag : (Tape.ofBits reply).current = none ∨ (Tape.ofBits reply).current = some true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    evalWithin program raw (budget raw.length) = PMF.pure (some [false]) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hBits⟩ := runs_wrong_tag n instanceBits reply hTag
  have hWith : HaltsWith program _ [false] used := ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program _ (budget _) used (haltsWithin _)
    (hWith.haltsWithin_of_no_randomBit no_randomBit)]
  exact hWith.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.ChooseWidthDecision
