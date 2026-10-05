import Foundation.Crypto.Semantics.Machine.ChooseFirstField
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChooseTwoFields

/-- Read the choose tag and both self-delimiting message fields using fixed
finite code. The first parser is the actual `ChooseFirstField` program; the
second is another invocation of `readDelimited` on its retained tapes.
No decoded Lean value is placed onto a tape for free. -/
def program : Program :=
  Program.withSubroutine [] ChooseFirstField.program
    (readDelimited.asSubroutine 23 40 ++ [.halt]) 23

theorem length : program.length = 41 := by decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

private theorem final_halt (c : Configuration) :
    RunsFor program (c.resumeAt 40)
      { c.resumeAt 40 with halted := true } 1 := by
  apply (RunsFor.zero _).succ
  have hLookup : program[40]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem canonical_first_start (first second state : List Bool) :
    let rest := FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ state
    let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false]
    let beforeOutput := some true :: first.reverse.map some
    ({ (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true } :
      Configuration).resumeAt 23 =
        (readDelimitedContextStart beforeInput beforeOutput second
          (state.map some)).rebasePc 23 := by
  dsimp only
  have hScan := ChooseFirstField.scan_delimit_append first
    (FiniteBitEncoding.delimit second ++ state)
  simp only [readDelimitedFinish, Configuration.resumeAt,
    Configuration.rebasePc, List.append_assoc]
  rw [hScan]
  cases second <;> cases state <;>
    simp [readDelimitedContextStart, FiniteBitEncoding.delimit]
  all_goals simp [Tape.ofBits, List.map_append]
  all_goals rfl

/-- On a canonical two-field response, both native parser invocations run on
their actual shared tapes. The final state retains the arbitrary reply state
at the input head and the two copied payloads with their success bits on the
output tape. -/
theorem runs_canonical (first second state : List Bool) :
    let rest := FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ state
    let raw := false :: rest
    let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false]
    let beforeOutput := some true :: first.reverse.map some
    let finish := readDelimitedContextFinish beforeInput beforeOutput second (state.map some)
    ∃ used ≤ ChooseFirstField.budget raw.length +
        readDelimitedSteps (FiniteBitEncoding.delimit second) + 2,
      RunsFor program (Configuration.initial raw)
        { finish.resumeAt 40 with halted := true } used := by
  dsimp only
  let rest := FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ state
  let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false]
  let beforeOutput := some true :: first.reverse.map some
  let firstFinish : Configuration :=
    { (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true }
  obtain ⟨firstUsed, hFirstUsed, hFirstRun⟩ := ChooseFirstField.runs_tag_false rest
  obtain ⟨returnedUsed, hReturnedUsed, hReturnedRun⟩ :=
    hFirstRun.withSubroutine_halted [] ChooseFirstField.program
      (readDelimited.asSubroutine 23 40 ++ [.halt]) 23
      (by change 0 ≤ 22; omega) rfl rfl
  have hFirst : RunsFor program (Configuration.initial (false :: rest))
      (firstFinish.resumeAt 23) returnedUsed := by
    simpa [program, firstFinish, Configuration.rebasePc] using hReturnedRun
  have hStart : firstFinish.resumeAt 23 =
      (readDelimitedContextStart beforeInput beforeOutput second
        (state.map some)).rebasePc 23 := by
    exact canonical_first_start first second state
  rw [hStart] at hFirst
  obtain ⟨secondUsed, hSecondUsed, hSecondRun⟩ :=
    (readDelimitedContext_runs beforeInput beforeOutput second (state.map some)).withSubroutine_halted
      (ChooseFirstField.program.asSubroutine 0 23) readDelimited [.halt] 40
      (by change 0 ≤ 16; omega) rfl rfl
  have hSecond : RunsFor program
      ((readDelimitedContextStart beforeInput beforeOutput second (state.map some)).rebasePc 23)
      ((readDelimitedContextFinish beforeInput beforeOutput second (state.map some)).resumeAt 40)
      secondUsed := by
    simpa only [program, Program.withSubroutine, List.nil_append,
      List.length_nil,
      Program.asSubroutine_length, ChooseFirstField.length,
      List.append_assoc, Nat.reduceAdd] using hSecondRun
  have hBound : firstUsed ≤ ChooseFirstField.budget (false :: rest).length := by
    have hSteps := readDelimitedSteps_le rest
    simp only [ChooseFirstField.budget, List.length_cons] at *
    omega
  change ∃ used ≤ ChooseFirstField.budget (false :: rest).length +
      readDelimitedSteps (FiniteBitEncoding.delimit second) + 2,
    RunsFor program (Configuration.initial (false :: rest))
      { (readDelimitedContextFinish beforeInput beforeOutput second
          (state.map some)).resumeAt 40 with halted := true } used
  refine ⟨returnedUsed + secondUsed + 1, by omega, ?_⟩
  exact (hFirst.trans hSecond).trans
    (final_halt (readDelimitedContextFinish beforeInput beforeOutput second (state.map some)))

/-- Contextual version for a response whose outer request prefix has already
been scanned. The earlier request cells remain on the input tape. -/
theorem runs_canonical_from (before : List (Option Bool))
    (first second state : List Bool) :
    let rest := FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ state
    let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: before
    let beforeOutput := some true :: first.reverse.map some
    let finish := readDelimitedContextFinish beforeInput beforeOutput second (state.map some)
    ∃ used ≤ ChooseFirstField.budget (false :: rest).length +
        readDelimitedSteps (FiniteBitEncoding.delimit second) + 2,
      RunsFor program
        ({ inputTape := { Tape.ofBits (false :: rest) with left := before } } :
          Configuration)
        { finish.resumeAt 40 with halted := true } used := by
  dsimp only
  let rest := FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ state
  let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++
    some false :: before
  let beforeOutput := some true :: first.reverse.map some
  let firstFinish : Configuration :=
    { (readDelimitedFinish (some false :: before) [] rest).resumeAt 19 with
      halted := true }
  obtain ⟨firstUsed, hFirstUsed, hFirstRun⟩ :=
    ChooseFirstField.runs_tag_false_from before rest
  obtain ⟨returnedUsed, hReturnedUsed, hReturnedRun⟩ :=
    hFirstRun.withSubroutine_halted [] ChooseFirstField.program
      (readDelimited.asSubroutine 23 40 ++ [.halt]) 23
      (by change 0 ≤ 22; omega) rfl rfl
  have hFirst : RunsFor program
      ({ inputTape := { Tape.ofBits (false :: rest) with left := before } } :
        Configuration)
      (firstFinish.resumeAt 23) returnedUsed := by
    simpa [program, firstFinish, Configuration.rebasePc] using hReturnedRun
  have hStart : firstFinish.resumeAt 23 =
      (readDelimitedContextStart beforeInput beforeOutput second
        (state.map some)).rebasePc 23 := by
    have hScan := ChooseFirstField.scan_delimit_append first
      (FiniteBitEncoding.delimit second ++ state)
    simp only [firstFinish, readDelimitedFinish,
      Configuration.resumeAt, Configuration.rebasePc]
    dsimp only [rest]
    simp only [List.append_assoc]
    rw [hScan]
    dsimp only [beforeInput, beforeOutput]
    cases second <;> cases state <;>
      simp [readDelimitedContextStart, FiniteBitEncoding.delimit]
    all_goals simp [Tape.ofBits, List.map_append]
    all_goals rfl
  rw [hStart] at hFirst
  obtain ⟨secondUsed, hSecondUsed, hSecondRun⟩ :=
    (readDelimitedContext_runs beforeInput beforeOutput second (state.map some)).withSubroutine_halted
      (ChooseFirstField.program.asSubroutine 0 23) readDelimited [.halt] 40
      (by change 0 ≤ 16; omega) rfl rfl
  have hSecond : RunsFor program
      ((readDelimitedContextStart beforeInput beforeOutput second (state.map some)).rebasePc 23)
      ((readDelimitedContextFinish beforeInput beforeOutput second (state.map some)).resumeAt 40)
      secondUsed := by
    simpa only [program, Program.withSubroutine, List.nil_append,
      List.length_nil, Program.asSubroutine_length, ChooseFirstField.length,
      List.append_assoc, Nat.reduceAdd] using hSecondRun
  have hBound : firstUsed ≤ ChooseFirstField.budget (false :: rest).length := by
    have hSteps := readDelimitedSteps_le rest
    simp only [ChooseFirstField.budget, List.length_cons] at *
    omega
  change ∃ used ≤ ChooseFirstField.budget (false :: rest).length +
      readDelimitedSteps (FiniteBitEncoding.delimit second) + 2,
    RunsFor program
      ({ inputTape := { Tape.ofBits (false :: rest) with left := before } } :
        Configuration)
      { (readDelimitedContextFinish beforeInput beforeOutput second
          (state.map some)).resumeAt 40 with halted := true } used
  refine ⟨returnedUsed + secondUsed + 1, by omega, ?_⟩
  exact (hFirst.trans hSecond).trans
    (final_halt (readDelimitedContextFinish beforeInput beforeOutput second (state.map some)))

private theorem first_runs (raw : List Bool) :
    ∃ finish used,
      used ≤ ChooseFirstField.budget raw.length ∧
      RunsFor ChooseFirstField.program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  cases raw with
  | nil =>
      refine ⟨_, 3, by simp [ChooseFirstField.budget],
        ChooseFirstField.runs_bad_tag [] (by simp), rfl⟩
  | cons tag rest =>
      cases tag with
      | true =>
          refine ⟨_, 3, by simp [ChooseFirstField.budget],
            ChooseFirstField.runs_bad_tag (true :: rest) (by simp), rfl⟩
      | false =>
          obtain ⟨used, hUsed, hRun⟩ := ChooseFirstField.runs_tag_false rest
          refine ⟨_, used, ?_, hRun, rfl⟩
          have hSteps := readDelimitedSteps_le rest
          simp only [ChooseFirstField.budget, List.length_cons]
          omega

private theorem initial_storage (raw : List Bool) :
    Machine.GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
  cases raw <;>
    simp [Machine.GuardedCompiler.sourceStorage, Configuration.initial,
      Tape.cells, Tape.ofBits] <;> omega

def budget (length : Nat) : Nat := 100 * (length + 1) + 100

/-- Both parser calls terminate on arbitrary finite input, even when the tag
or either delimiter is malformed or when retained tapes contain blanks. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨first, used₁, hUsed₁, run₁, hHalt₁⟩ := first_runs raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseFirstField.program
      (readDelimited.asSubroutine 23 40 ++ [.halt]) 23
      (by change 0 ≤ 22; omega) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (first.resumeAt 23) returned₁ := by
    simpa [program, Configuration.rebasePc] using embedded₁
  let secondStart : Configuration :=
    { inputTape := first.inputTape, outputTape := first.outputTape }
  obtain ⟨second, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    readDelimited_terminates_from_anyTape first.inputTape first.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted (ChooseFirstField.program.asSubroutine 0 23)
      readDelimited [.halt] 40 (by change 0 ≤ 16; omega) rfl hHalt₂
  have secondRun : RunsFor program (first.resumeAt 23)
      (second.resumeAt 40) returned₂ := by
    simpa only [program, Program.withSubroutine, List.nil_append,
      List.length_nil, Program.asSubroutine_length,
      ChooseFirstField.length, List.append_assoc, Nat.reduceAdd,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial := initial_storage raw
  have hCells : first.inputTape.cells ≤ raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage hInitial
    omega
  have hBudget : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    unfold budget ChooseFirstField.budget at *
    omega
  have hRun : RunsFor program (Configuration.initial raw)
      { second.resumeAt 40 with halted := true }
      (returned₁ + returned₂ + 1) :=
    (firstRun.trans secondRun).trans (final_halt second)
  exact ⟨_, returned₁ + returned₂ + 1, hBudget, hRun, rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHaltsWith : HaltsWith program raw finish.outputBits used :=
    ⟨_, run, hHalt, rfl⟩
  exact (hHaltsWith.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

/-- A contextual stopping bound for the same fixed code. This permits an
outer parser to leave arbitrary earlier fields and blank scratch cells on
the tapes before the choose-response fields are read. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ finish used,
      used ≤ 200 * (input.cells + output.cells + 1) + 200 ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  obtain ⟨first, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseFirstField.terminates_from_anyTape input output
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseFirstField.program
      (readDelimited.asSubroutine 23 40 ++ [.halt]) 23
      (by change 0 ≤ 22; omega) rfl hHalt₁
  have firstRun : RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      (first.resumeAt 23) returned₁ := by
    simpa [program, Configuration.rebasePc] using embedded₁
  obtain ⟨second, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    readDelimited_terminates_from_anyTape first.inputTape first.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted (ChooseFirstField.program.asSubroutine 0 23)
      readDelimited [.halt] 40 (by change 0 ≤ 16; omega) rfl hHalt₂
  have secondRun : RunsFor program (first.resumeAt 23)
      (second.resumeAt 40) returned₂ := by
    simpa only [program, Program.withSubroutine, List.nil_append,
      List.length_nil, Program.asSubroutine_length,
      ChooseFirstField.length, List.append_assoc, Nat.reduceAdd,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hCells : first.inputTape.cells ≤ input.cells + output.cells + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage
    omega
  have hBound : returned₁ + returned₂ + 1 ≤
      200 * (input.cells + output.cells + 1) + 200 := by omega
  have run : RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      { second.resumeAt 40 with halted := true }
      (returned₁ + returned₂ + 1) :=
    (firstRun.trans secondRun).trans (final_halt second)
  exact ⟨_, returned₁ + returned₂ + 1, hBound, run, rfl⟩

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact ((PolynomiallyBounded.const 100).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 100)

theorem canonical_output (first second state : List Bool) :
    let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false]
    let beforeOutput := some true :: first.reverse.map some
    (readDelimitedContextFinish beforeInput beforeOutput second
      (state.map some)).outputBits = first ++ [true] ++ second ++ [true] := by
  simp [readDelimitedContextFinish, Configuration.outputBits, Tape.bits,
    List.reverse_append, List.map_reverse, List.filterMap_append,
    List.append_assoc]

/-- Evaluator equality for the two native parser passes. The output is a
staging representation with a success bit after each copied field; it is not
yet the finished normalizer response. -/
theorem eval_canonical (first second state : List Bool) :
    let raw := false :: (FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ state)
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (first ++ [true] ++ second ++ [true])) := by
  dsimp only
  let raw := false :: (FiniteBitEncoding.delimit first ++
    FiniteBitEncoding.delimit second ++ state)
  let beforeInput := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false]
  let beforeOutput := some true :: first.reverse.map some
  let finish := readDelimitedContextFinish beforeInput beforeOutput second (state.map some)
  obtain ⟨used, _hUsed, run⟩ := runs_canonical first second state
  have hOutput : ({ finish.resumeAt 40 with halted := true } : Configuration).outputBits =
      first ++ [true] ++ second ++ [true] := by
    change finish.outputBits = _
    exact canonical_output first second state
  have hHalt : HaltsWith program raw (first ++ [true] ++ second ++ [true]) used :=
    ⟨_, run, rfl, hOutput⟩
  rw [evalWithin_eq_of_haltsWithin program raw (budget raw.length) used
    (haltsWithin raw) (hHalt.haltsWithin_of_no_randomBit no_randomBit)]
  exact hHalt.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.ChooseTwoFields
