import Foundation.Crypto.Semantics.Machine.ChooseFirstWidthCheck
import Foundation.Crypto.Semantics.Machine.ChooseSecondWidthCheck
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChooseTwoWidths

private def firstReturn : Nat := ChooseFirstWidthCheck.program.length + 1
private def finalReturn : Nat := firstReturn + ChooseSecondWidthCheck.program.length + 1

/-- Two native width checks share the same copied instance-code counter.
The first failure is terminal; a successful first scan rewinds that counter
before checking the second field. -/
def program : Program :=
  ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn ++
    ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseFirstWidthCheck.program
      (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
      ChooseSecondWidthCheck.program [.halt] finalReturn := by
  simp [program, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalReturn)
      { c.resumeAt finalReturn with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def start (beforeInput : List (Option Bool))
    (counter first second tail : List Bool) : Configuration :=
  ChooseFirstWidthCheck.start beforeInput [none] counter
    (false :: FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ tail)

/-- Complete two-stage status specification for arbitrary raw fields. -/
theorem runs_raw_layout (beforeInput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used,
      RunsFor program
        (ChooseFirstWidthCheck.start beforeInput [none] counter (false :: raw)) target used ∧
      target.halted = true ∧ target.outputTape.current = some
        ((FiniteBitEncoding.undelimit raw).any (fun pair =>
          decide (pair.1.length = width) &&
            (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape.Equivalent
          { left := consumed.reverse.map some ++ [none],
            current := target.outputTape.current, right := (Tape.ofBits suffix).right } := by
  by_cases hFirstDecision : (FiniteBitEncoding.undelimit raw).any
      (fun pair => decide (pair.1.length = width)) = true
  · cases hParse : FiniteBitEncoding.undelimit raw with
    | none => simp [hParse] at hFirstDecision
    | some pair =>
      rcases pair with ⟨first, remaining⟩
      have hFirst : first.length = width := by simpa [hParse] using hFirstDecision
      have hRaw := FiniteBitEncoding.delimit_append_of_undelimit hParse
      rw [← hRaw]
      have firstRun := ChooseFirstWidthCheck.runs_matching_layout
        beforeInput [none] counter first
        remaining
        (by omega)
      obtain ⟨firstTarget, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ := firstRun
      let firstFinish := DelimitedTripleWidthCheck.finish
        (some false :: beforeInput) [none] counter first
        remaining
      obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
        run₁.withSubroutine_halted [] ChooseFirstWidthCheck.program
          (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
          firstReturn (Nat.zero_le _) rfl hHalt₁
      have firstEmbedded : RunsFor program
          (ChooseFirstWidthCheck.start beforeInput [none] counter (false :: FiniteBitEncoding.delimit first ++ remaining))
          (firstTarget.resumeAt firstReturn) returned₁ := by
        simpa only [← first_layout, Configuration.rebasePc,
          List.length_nil, Nat.zero_add, start, List.append_assoc] using embedded₁
      obtain ⟨finish, used₂, run₂, hHalt₂, hStatus₂, hLayout₂⟩ :=
        ChooseSecondWidthCheck.runs_second_raw_layout beforeInput width counter
          first remaining hCounter
      have hJoin :
          (firstTarget.resumeAt firstReturn) =
          (({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } :
            Configuration).rebasePc firstReturn) := by
        simp [Configuration.resumeAt, Configuration.rebasePc, hInput₁, hOutput₁,
          firstFinish]
      rw [hJoin] at firstEmbedded
      obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
        run₂.withSubroutine_halted
          (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
          ChooseSecondWidthCheck.program [.halt] finalReturn
          (Nat.zero_le _) rfl hHalt₂
      have secondEmbedded : RunsFor program
          (({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } :
            Configuration).rebasePc firstReturn)
          (finish.resumeAt finalReturn) returned₂ := by
        simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
      refine ⟨{ finish.resumeAt finalReturn with halted := true },
        returned₁ + returned₂ + 1, ?_, rfl, ?_, ?_⟩
      · exact (firstEmbedded.trans secondEmbedded).succ (final_step finish)
      · simpa [Configuration.resumeAt, hFirst] using hStatus₂
      · simpa [Configuration.resumeAt] using hLayout₂
  · have hFalseDecision : (FiniteBitEncoding.undelimit raw).any
        (fun pair => decide (pair.1.length = width)) = false := by
      cases h : (FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width)) with
      | false => rfl
      | true => exact False.elim (hFirstDecision h)
    have hBothFalse : (FiniteBitEncoding.undelimit raw).any (fun pair =>
        decide (pair.1.length = width) &&
          (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width))) = false := by
      cases hParse : FiniteBitEncoding.undelimit raw with
      | none => simp [hParse]
      | some pair =>
          rcases pair with ⟨first, remaining⟩
          have hFirst : first.length ≠ width := by
            intro hLength
            apply hFirstDecision
            simp [hParse, hLength]
          simp [hParse, hFirst]
    obtain ⟨firstTarget, used₁, _hUsed₁, run₁, hHalt₁, hStatus₁, hLayout₁⟩ :=
      ChooseFirstWidthCheck.runs_raw_layout beforeInput [none] width counter raw hCounter
    have hFailed : firstTarget.outputTape.current = some false := by
      simpa [hFalseDecision] using hStatus₁
    obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
      run₁.withSubroutine_halted [] ChooseFirstWidthCheck.program
        (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
        firstReturn (Nat.zero_le _) rfl hHalt₁
    have firstEmbedded : RunsFor program
        (ChooseFirstWidthCheck.start beforeInput [none] counter (false :: raw))
        (firstTarget.resumeAt firstReturn) returned₁ := by
      simpa only [← first_layout, Configuration.rebasePc,
        List.length_nil, Nat.zero_add, start, List.append_assoc] using embedded₁
    obtain ⟨finish, run₂, hHalt₂, hStatus₂, hTape₂⟩ :=
      ChooseSecondWidthCheck.rejects_failed_first_layout
        firstTarget.inputTape firstTarget.outputTape hFailed
    obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
      run₂.withSubroutine_halted
        (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
        ChooseSecondWidthCheck.program [.halt] finalReturn
        (Nat.zero_le _) rfl hHalt₂
    have secondEmbedded : RunsFor program
        (firstTarget.resumeAt firstReturn)
        (finish.resumeAt finalReturn) returned₂ := by
      simpa [second_layout, firstReturn, Program.asSubroutine_length,
        Configuration.resumeAt, Configuration.rebasePc] using embedded₂
    refine ⟨{ finish.resumeAt finalReturn with halted := true },
      returned₁ + returned₂ + 1, ?_, rfl, ?_, ?_⟩
    · exact (firstEmbedded.trans secondEmbedded).succ (final_step finish)
    · simpa [Configuration.resumeAt, hBothFalse] using hStatus₂
    · obtain ⟨consumed, suffix, hParts, hTape₁⟩ := hLayout₁
      refine ⟨consumed, suffix, hParts, ?_⟩
      have hTape : finish.outputTape =
          { left := consumed.reverse.map some ++ [none],
            current := some false, right := (Tape.ofBits suffix).right } := by
        rw [hTape₂, hTape₁]
        rfl
      simpa [Configuration.resumeAt, hTape] using
        (Tape.Equivalent.refl finish.outputTape)

theorem runs_raw_status (beforeInput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used,
      RunsFor program
        (ChooseFirstWidthCheck.start beforeInput [none] counter (false :: raw)) target used ∧
      target.halted = true ∧ target.outputTape.current = some
        ((FiniteBitEncoding.undelimit raw).any (fun pair =>
          decide (pair.1.length = width) &&
            (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))) := by
  obtain ⟨target, used, run, hHalt, hStatus, _⟩ :=
    runs_raw_layout beforeInput width counter raw hCounter
  exact ⟨target, used, run, hHalt, hStatus⟩

/-- A successful halted run on arbitrary raw fields exposes both
complete fixed-width fields and the exact trailing state. This is the
inverse needed before applying the numeric and subgroup check theorems. -/
theorem fields_of_accepted_run (beforeInput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      (ChooseFirstWidthCheck.start beforeInput [none] counter (false :: raw)) target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ first second tail,
      FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail = raw ∧
      first.length = width ∧ second.length = width := by
  obtain ⟨checked, steps, checkRun, checkHalt, hStatus⟩ :=
    runs_raw_status beforeInput width counter raw hCounter
  have hSame := run.halted_finish_eq_of_no_randomBit checkRun hHalt checkHalt no_randomBit
  rw [← hSame, hAccept] at hStatus
  cases hFirstParse : FiniteBitEncoding.undelimit raw with
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
          exact ⟨first, second, tail, by simpa [List.append_assoc] using hFirstShape, hLengths⟩

/-- Canonical-field specialization of the all-raw status theorem. -/
theorem runs_width_status (beforeInput : List (Option Bool))
    (width : Nat) (counter first second tail : List Bool)
    (hCounter : counter.length = 3 * width) :
    ∃ target used,
      RunsFor program (start beforeInput counter first second tail)
        target used ∧ target.halted = true ∧
      target.outputTape.current =
        some (decide (first.length = width ∧ second.length = width)) := by
  obtain ⟨target, used, run, hHalt, hStatus⟩ := runs_raw_status beforeInput width counter
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ tail) hCounter
  refine ⟨target, used, run, hHalt, ?_⟩
  by_cases hFirst : first.length = width <;> by_cases hSecond : second.length = width <;>
    simpa [hFirst, hSecond] using hStatus

/-- The combined checker retains the first guard's rejection of blank or
guess-stage replies. The second width stage cannot turn this failure into
acceptance. This trace holds on arbitrary physical tapes. -/
theorem rejects_wrong_tag_layout (input output : Tape)
    (hTag : input.current = none ∨ input.current = some true) :
    ∃ target used, used ≤ 7 ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) := by
  obtain ⟨firstTarget, run₁, hHalt₁, hFailed, hOutput₁⟩ :=
    ChooseFirstWidthCheck.rejects_wrong_tag_layout input output hTag
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseFirstWidthCheck.program
      (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstEmbedded : RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      (firstTarget.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, run₂, hHalt₂, hStatus₂, hOutput₂⟩ :=
    ChooseSecondWidthCheck.rejects_failed_first_layout
      firstTarget.inputTape firstTarget.outputTape hFailed
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
      ChooseSecondWidthCheck.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondEmbedded : RunsFor program
      (firstTarget.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  refine ⟨{ finish.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, by omega, ?_, rfl, ?_, ?_⟩
  · exact (firstEmbedded.trans secondEmbedded).succ (final_step finish)
  · simpa [Configuration.resumeAt] using hStatus₂

  · simpa [Configuration.resumeAt, hOutput₂, hOutput₁, Tape.write]

/-- A wrong-stage tag remains rejected through both width stages. -/
theorem rejects_wrong_tag (input output : Tape)
    (hTag : input.current = none ∨ input.current = some true) :
    ∃ target used, used ≤ 7 ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true ∧ target.outputTape.current = some false := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, _⟩ := rejects_wrong_tag_layout input output hTag
  exact ⟨target, used, hUsed, run, hHalt, hStatus⟩

/-- After two successful width scans, the input head is at the trailing
state and the output head is just after the retained instance code. These
physical positions are preserved for subsequent validity checks. -/
theorem runs_matching_layout (beforeInput : List (Option Bool))
    (counter first second tail : List Bool)
    (hFirst : counter.length = 3 * first.length)
    (hSecond : counter.length = 3 * second.length) :
    let beforeSecond := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: beforeInput
    let secondFinish := DelimitedTripleWidthCheck.finish
      beforeSecond [none] counter second tail
    ∃ target used,
      RunsFor program (start beforeInput counter first second tail)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent secondFinish.inputTape ∧
      target.outputTape.Equivalent secondFinish.outputTape := by
  dsimp only
  let firstFinish := DelimitedTripleWidthCheck.finish
    (some false :: beforeInput) [none] counter first
    (FiniteBitEncoding.delimit second ++ tail)
  obtain ⟨firstTarget, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    ChooseFirstWidthCheck.runs_matching_layout beforeInput [none]
      counter first (FiniteBitEncoding.delimit second ++ tail) hFirst
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseFirstWidthCheck.program
      (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstEmbedded : RunsFor program
      (start beforeInput counter first second tail)
      (firstTarget.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, start, List.append_assoc] using embedded₁
  obtain ⟨finish, used₂, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    ChooseSecondWidthCheck.runs_second_matching_layout beforeInput
      counter first second tail hSecond
  have hJoin :
      (firstTarget.resumeAt firstReturn) =
      (({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } :
        Configuration).rebasePc firstReturn) := by
    simp [Configuration.resumeAt, Configuration.rebasePc, hInput₁, hOutput₁,
      firstFinish]
  rw [hJoin] at firstEmbedded
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
      ChooseSecondWidthCheck.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondEmbedded : RunsFor program
      (({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } :
        Configuration).rebasePc firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  refine ⟨{ finish.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, ?_, rfl, ?_, ?_⟩
  · exact (firstEmbedded.trans secondEmbedded).succ (final_step finish)
  · simpa [Configuration.resumeAt] using hInput₂
  · simpa [Configuration.resumeAt] using hOutput₂

/-- The two guarded width scans stop on arbitrary finite retained tapes.
This bound counts the first scan, the conditional rewind, and the second. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ target used,
      used ≤ 1000000 * (input.cells + output.cells + 1) + 1000000 ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  obtain ⟨middle, used₁, hUsed₁, firstRun, hHalt₁⟩ :=
    ChooseFirstWidthCheck.terminates_from_anyTape input output
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    firstRun.withSubroutine_halted [] ChooseFirstWidthCheck.program
      (ChooseSecondWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstEmbedded : RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      (middle.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, secondRun, hHalt₂⟩ :=
    ChooseSecondWidthCheck.terminates_from_anyTape
      middle.inputTape middle.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    secondRun.withSubroutine_halted
      (ChooseFirstWidthCheck.program.asSubroutine 0 firstReturn)
      ChooseSecondWidthCheck.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondEmbedded : RunsFor program (middle.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run firstRun
  have hMiddle : middle.inputTape.cells + middle.outputTape.cells ≤
      input.cells + output.cells + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage
    omega
  have hBound : returned₁ + returned₂ + 1 ≤
      1000000 * (input.cells + output.cells + 1) + 1000000 := by
    dsimp only [Tape.cells] at *
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstEmbedded.trans secondEmbedded).succ (final_step finish), rfl⟩

end Machine.ChooseTwoWidths
