import Foundation.Crypto.Semantics.Machine.FramedInstanceResponseReady
import Foundation.Crypto.Semantics.Machine.ChooseTwoWidths
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChooseTwoWidthsPrefix

private def firstReturn : Nat := FramedInstanceResponseReady.program.length + 1
private def finalReturn : Nat := firstReturn + ChooseTwoWidths.program.length + 1

/-- One fixed program copies and rewinds the instance code, reads the
response frame, checks the choose tag, and tests both element widths.
The remaining validity tests and output reconstruction are separate work. -/
def program : Program :=
  FramedInstanceResponseReady.program.asSubroutine 0 firstReturn ++
    ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceResponseReady.program
      (ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseTwoWidths.program [.halt] finalReturn := by
  simp [program, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalReturn)
      { c.resumeAt finalReturn with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat := 100000000000 * (length + 1) + 100000000000

/-- Wrong-stage or empty responses are rejected after their outer frame is
read. The conclusion is about the same fixed finite program as the width
checks, and does not assume that either element field can be decoded. -/
theorem runs_wrong_tag_layout (n : Nat) (instanceBits reply : List Bool)
    (hTag : (Tape.ofBits reply).current = none ∨
      (Tape.ofBits reply).current = some true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false ∧
      finish.outputTape = ((({ right := instanceBits.map some ++ [none] } : Tape).moveRight).write (some false)) := by
  dsimp only
  obtain ⟨after, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedInstanceResponseReady.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  have hActualTag : after.inputTape.current = none ∨
      after.inputTape.current = some true := by
    simpa only [hInput₁] using hTag
  obtain ⟨finish, used₂, _hUsed₂, run₂, hHalt₂, hStatus₂, hOutput₂⟩ :=
    ChooseTwoWidths.rejects_wrong_tag_layout after.inputTape after.outputTape hActualTag
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseTwoWidths.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  refine ⟨{ finish.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, ?_, rfl, ?_, ?_⟩
  · exact (firstRun.trans secondRun).succ (final_step finish)
  · simpa [Configuration.resumeAt] using hStatus₂

  · simpa [Configuration.resumeAt, hOutput₂, hOutput₁]

/-- Status-only projection of the complete native wrong-tag layout. -/
theorem runs_wrong_tag (n : Nat) (instanceBits reply : List Bool)
    (hTag : (Tape.ofBits reply).current = none ∨ (Tape.ofBits reply).current = some true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used, RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  obtain ⟨finish, used, run, hHalt, hStatus, _⟩ := runs_wrong_tag_layout n instanceBits reply hTag
  exact ⟨finish, used, run, hHalt, hStatus⟩

/-- On a correctly framed response with a choose tag, the status cell is
true exactly when both element fields have the width advertised by the
three-field instance code. The rest of the reply is not consumed by magic. -/
theorem runs_raw_layout (n width : Nat) (instanceBits payload : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: payload
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current =
        some ((FiniteBitEncoding.undelimit payload).any (fun pair =>
          decide (pair.1.length = width) &&
            (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))) ∧
      ∃ consumed suffix, instanceBits = consumed ++ suffix ∧
        finish.outputTape.Equivalent
          { left := consumed.reverse.map some ++ [none],
            current := finish.outputTape.current, right := (Tape.ofBits suffix).right } := by
  dsimp only
  let reply := false :: payload
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨after, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedInstanceResponseReady.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  let expected := ChooseFirstWidthCheck.start before [none] instanceBits (false :: payload)
  have hEquivalent : (expected.rebasePc firstReturn).Equivalent
      (after.resumeAt firstReturn) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected, ChooseTwoWidths.start, before,
        Configuration.rebasePc, Configuration.resumeAt, hInput₁,
        ChooseFirstWidthCheck.start, reply] using
        (Tape.Equivalent.refl ({ Tape.ofBits reply with left := before } : Tape))
    · have hRew := rewindScratchFinish_input_equivalent [] instanceBits after.inputTape
      simpa [expected, ChooseTwoWidths.start, ChooseFirstWidthCheck.start,
        Configuration.rebasePc, Configuration.resumeAt, hOutput₁,
        rewindScratchFinish] using hRew.symm
  obtain ⟨finish, used₂, checkRun, hHalt₂, hStatus, hLayout⟩ :=
    ChooseTwoWidths.runs_raw_layout before width
      instanceBits payload hLength
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    checkRun.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseTwoWidths.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have checkEmbedded : RunsFor program (expected.rebasePc firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    checkEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalReturn := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := by
    exact hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalReturn]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_, ?_⟩
  · exact (hActual.2.2.2.1.symm).trans (by
      simpa [Configuration.resumeAt] using hStatus)
  · obtain ⟨consumed, suffix, hParts, hTape⟩ := hLayout
    refine ⟨consumed, suffix, hParts, ?_⟩
    have eqTape : actual.outputTape.Equivalent finish.outputTape := by
      simpa [Configuration.resumeAt] using hActual.2.2.2.symm
    have eqCurrent : finish.outputTape.current = actual.outputTape.current := by
      simpa [Configuration.resumeAt] using hActual.2.2.2.1
    simpa only [eqCurrent] using eqTape.trans hTape

theorem runs_raw_status (n width : Nat) (instanceBits payload : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: payload
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current =
        some ((FiniteBitEncoding.undelimit payload).any (fun pair =>
          decide (pair.1.length = width) &&
            (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))) := by
  obtain ⟨finish, used, run, hHalt, hStatus, _⟩ :=
    runs_raw_layout n width instanceBits payload hLength
  exact ⟨finish, used, run, hHalt, hStatus⟩

/-- Canonical-field projection of the complete framed width specification. -/
theorem runs_width_status (n width : Nat) (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current =
        some (decide (first.length = width ∧ second.length = width)) := by
  obtain ⟨finish, used, run, hHalt, hStatus⟩ := runs_raw_status n width instanceBits
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail) hLength
  refine ⟨finish, used, run, hHalt, ?_⟩
  by_cases hFirst : first.length = width <;> by_cases hSecond : second.length = width <;>
    simpa [hFirst, hSecond] using hStatus

/-- The framed checker cannot accept a malformed choose reply. Its
success entails two complete fixed-width fields and preserves their exact
state suffix in the mathematical decomposition of the original reply. -/
theorem fields_of_accepted_run (n width : Nat) (instanceBits reply : List Bool)
    (hLength : instanceBits.length = 3 * width)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)) target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ first second tail,
      false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail = reply ∧
      first.length = width ∧ second.length = width := by
  have rejectImpossible (hTag : (Tape.ofBits reply).current = none ∨
      (Tape.ofBits reply).current = some true) : False := by
    obtain ⟨checked, steps, checkRun, checkHalt, hStatus⟩ := runs_wrong_tag n instanceBits reply hTag
    have hSame := run.halted_finish_eq_of_no_randomBit checkRun hHalt checkHalt no_randomBit
    rw [← hSame, hAccept] at hStatus
    contradiction
  cases reply with
  | nil => exact False.elim (rejectImpossible (Or.inl rfl))
  | cons tag payload =>
      cases tag with
      | true => exact False.elim (rejectImpossible (Or.inr rfl))
      | false =>
          obtain ⟨checked, steps, checkRun, checkHalt, hStatus⟩ :=
            runs_raw_status n width instanceBits payload hLength
          have hSame := run.halted_finish_eq_of_no_randomBit checkRun hHalt checkHalt no_randomBit
          rw [← hSame, hAccept] at hStatus
          cases hFirstParse : FiniteBitEncoding.undelimit payload with
          | none => simp [hFirstParse] at hStatus
          | some pair =>
              rcases pair with ⟨first, remaining⟩
              cases hSecondParse : FiniteBitEncoding.undelimit remaining with
              | none => simp [hFirstParse, hSecondParse] at hStatus
              | some next =>
                  rcases next with ⟨second, tail⟩
                  have hLengths : first.length = width ∧ second.length = width := by
                    simpa [hFirstParse, hSecondParse] using hStatus.symm
                  have hFirstShape := FiniteBitEncoding.delimit_append_of_undelimit hFirstParse
                  have hSecondShape := FiniteBitEncoding.delimit_append_of_undelimit hSecondParse
                  rw [← hSecondShape] at hFirstShape
                  exact ⟨first, second, tail,
                    by simpa [List.append_assoc] using congrArg (List.cons false) hFirstShape,
                    hLengths⟩

/-- On two width-matching fields, the connected parser exposes the retained
instance and trailing response state on the actual tapes. The layout is
stated up to blank-tape equivalence because the native rewind leaves a
physically represented padding cell. -/
theorem runs_matching_layout (n width : Nat)
    (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width)
    (hFirst : first.length = width) (hSecond : second.length = width) :
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let before := some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
    let beforeSecond := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: before
    let secondFinish := DelimitedTripleWidthCheck.finish
      beforeSecond [none] instanceBits second tail
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.inputTape.Equivalent secondFinish.inputTape ∧
      finish.outputTape.Equivalent secondFinish.outputTape := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨after, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedInstanceResponseReady.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  let expected := ChooseTwoWidths.start before instanceBits first second tail
  have hEquivalent : (expected.rebasePc firstReturn).Equivalent
      (after.resumeAt firstReturn) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected, ChooseTwoWidths.start, before,
        Configuration.rebasePc, Configuration.resumeAt, hInput₁,
        ChooseFirstWidthCheck.start, reply] using
        (Tape.Equivalent.refl ({ Tape.ofBits reply with left := before } : Tape))
    · have hRew := rewindScratchFinish_input_equivalent [] instanceBits after.inputTape
      simpa [expected, ChooseTwoWidths.start, ChooseFirstWidthCheck.start,
        Configuration.rebasePc, Configuration.resumeAt, hOutput₁,
        rewindScratchFinish] using hRew.symm
  obtain ⟨innerFinish, used₂, checkRun, hHalt₂, hInput₂, hOutput₂⟩ :=
    ChooseTwoWidths.runs_matching_layout before instanceBits first second tail
      (by omega) (by omega)
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    checkRun.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseTwoWidths.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have checkEmbedded : RunsFor program (expected.rebasePc firstReturn)
      (innerFinish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    checkEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalReturn := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalReturn]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_, ?_⟩
  · exact hActual.2.2.1.symm.trans (by
      simpa [Configuration.resumeAt, before, reply, frame,
        FiniteBitEncoding.delimit, List.map_append] using hInput₂)
  · exact hActual.2.2.2.symm.trans (by
      simpa [Configuration.resumeAt, before, reply, frame,
        FiniteBitEncoding.delimit, List.map_append] using hOutput₂)

/-- The connected prefix stops on all finite inputs, including malformed
outer frames, wrong-stage tags, and truncated element delimiters. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    FramedInstanceResponseReady.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseTwoWidths.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseTwoWidths.terminates_from_anyTape
      after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseTwoWidths.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : Machine.GuardedCompiler.sourceStorage
      (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;>
      simp [Machine.GuardedCompiler.sourceStorage, Configuration.initial,
        Tape.cells, Tape.ofBits] <;> omega
  have hCells : after.inputTape.cells + after.outputTape.cells ≤
      raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage hInitial
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, FramedInstanceResponseReady.budget] at *
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstRun.trans secondRun).succ (final_step finish), rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

/-- The common all-input polynomial budget observes the same width status
as the exact native trace, even if the trace stops before that budget. -/
theorem eval_width_status (n width : Nat) (instanceBits first second tail : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    (evalConfigWithin program (Configuration.initial raw)
      (budget raw.length)).map (fun c => c.outputTape.current) =
      PMF.pure (some (decide (first.length = width ∧ second.length = width))) := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨finish, used, run, hHalt, hStatus⟩ :=
    runs_width_status n width instanceBits first second tail hLength
  have hAtUsed : HaltsWithin program raw used :=
    run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  have hAtBudget := haltsWithin raw
  let common := max used (budget raw.length)
  have hUsedStable : evalConfigWithin program (Configuration.initial raw) common =
      evalConfigWithin program (Configuration.initial raw) used := by
    have h := evalConfigWithin_stable program raw used (common - used) hAtUsed
    simpa [common, Nat.add_sub_of_le (le_max_left used (budget raw.length))] using h
  have hBudgetStable : evalConfigWithin program (Configuration.initial raw) common =
      evalConfigWithin program (Configuration.initial raw)
        (budget raw.length) := by
    have h := evalConfigWithin_stable program raw (budget raw.length)
      (common - budget raw.length) hAtBudget
    simpa [common, Nat.add_sub_of_le (le_max_right used (budget raw.length))] using h
  rw [← hBudgetStable, hUsedStable,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hStatus]

theorem budget_polynomial : PolynomiallyBounded budget := by
  unfold budget
  exact ((PolynomiallyBounded.const 100000000000).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 100000000000)

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomial, haltsWithin⟩

end Machine.ChooseTwoWidthsPrefix
