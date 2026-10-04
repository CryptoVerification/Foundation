import Foundation.Machine.DelimitedTripleWidthCheck

namespace Machine.ChooseFirstWidthCheck

private def checkEntry : Nat := 2
private def finalPc : Nat := checkEntry + DelimitedTripleWidthCheck.program.length + 1
private def rejectPc : Nat := finalPc + 1

private def guard : Program :=
  [.branch .input rejectPc 1 rejectPc, .moveRight .input]

/-- Inspect the choose tag and compare the first delimited element field
with one third of the instance-code cells. Wrong-stage and blank tags leave
a false status; no mathematical decoder is invoked. -/
def program : Program :=
  guard ++ DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
    [.halt, .write .output false, .halt]

private theorem check_layout : program =
    Program.withSubroutine guard DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc := by
  simp [program, Program.withSubroutine, guard, checkEntry]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def start (beforeInput beforeOutput : List (Option Bool))
    (counter reply : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits reply with left := beforeInput },
    outputTape := { Tape.ofBits counter with left := beforeOutput } }

private theorem guard_accept (input output : Tape)
    (hTag : input.current = some false) :
    RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := checkEntry, inputTape := input.moveRight, outputTape := output } :
        Configuration) 2 := by
  let source : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { source with pc := 1 }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, guard, source, selected,
      Instruction.next, Configuration.tape, hTag]
  have h1 : Step program selected
      ({ pc := checkEntry, inputTape := input.moveRight, outputTape := output } :
        Configuration) := by
    simp [Step, successors, next, program, guard, source, selected,
      checkEntry, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  exact ((RunsFor.zero _).succ h0).succ h1

private theorem guard_reject_layout (input output : Tape)
    (hTag : input.current = none ∨ input.current = some true) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧
      target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) := by
  let source : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { source with pc := rejectPc }
  let written : Configuration :=
    { selected with pc := rejectPc + 1, outputTape := output.write (some false) }
  have h0 : Step program source selected := by
    rcases hTag with hBlank | hTrue
    · simp [Step, successors, next, program, guard, source, selected,
        Instruction.next, Configuration.tape, hBlank]
    · simp [Step, successors, next, program, guard, source, selected,
        Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected written := by
    have hLookup : program[rejectPc]? = some (.write .output false) := by
      native_decide
    simp [Step, successors, next, source, selected, written, hLookup,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step program written { written with halted := true } := by
    have hLookup : program[rejectPc + 1]? = some .halt := by native_decide
    simp [Step, successors, next, written, hLookup, Instruction.next]
  exact ⟨_, (((RunsFor.zero _).succ h0).succ h1).succ h2, rfl,
    by simp [written, selected, Tape.write], rfl⟩

private theorem guard_reject (input output : Tape)
    (h : input.current = none ∨ input.current = some true) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧ target.outputTape.current = some false := by
  obtain ⟨target, run, hHalt, hStatus, _⟩ := guard_reject_layout input output h
  exact ⟨target, run, hHalt, hStatus⟩

/-- Wrong-stage and absent tags are rejected by the actual guard, before
any element payload is scanned. -/
theorem rejects_wrong_tag (input output : Tape)
    (hTag : input.current = none ∨ input.current = some true) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧
      target.outputTape.current = some false :=
  guard_reject input output hTag

/-- Rejection writes the real status cell and retains all other workspace cells. -/
theorem rejects_wrong_tag_layout (input output : Tape)
    (hTag : input.current = none ∨ input.current = some true) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧ target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) :=
  guard_reject_layout input output hTag

/-- All finite first-field inputs, including unterminated payloads, are
checked by the same finite stage-tag guard and triple-width scanner. -/
theorem runs_raw_layout (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 9 ∧
      RunsFor program (start beforeInput beforeOutput counter (false :: raw)) target used ∧
      target.halted = true ∧ target.outputTape.current = some
        ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape =
          { left := consumed.reverse.map some ++ beforeOutput,
            current := target.outputTape.current, right := (Tape.ofBits suffix).right } := by
  let input : Tape := { Tape.ofBits (false :: raw) with left := beforeInput }
  let output : Tape := { Tape.ofBits counter with left := beforeOutput }
  have hGuard := guard_accept input output rfl
  obtain ⟨checked, used, hUsed, run, hHalt, hStatus, hLayout⟩ :=
    DelimitedTripleWidthCheck.runs_raw_decision_layout (some false :: beforeInput)
      beforeOutput width counter raw hCounter
  let source : Configuration :=
    { inputTape := { Tape.ofBits raw with left := some false :: beforeInput }, outputTape := output }
  have hJoin : ({ pc := checkEntry, inputTape := input.moveRight, outputTape := output } : Configuration) =
      source.rebasePc checkEntry := by
    cases raw <;> simp [input, source, Tape.ofBits, Tape.moveRight, Configuration.rebasePc]
  rw [hJoin] at hGuard
  obtain ⟨returned, hReturned, embedded⟩ := run.withSubroutine_halted guard
    DelimitedTripleWidthCheck.program [.halt, .write .output false, .halt] finalPc
    (Nat.zero_le _) rfl hHalt
  have checkRun : RunsFor program (source.rebasePc checkEntry) (checked.resumeAt finalPc) returned := by
    simpa [check_layout, guard, checkEntry, source, output] using embedded
  refine ⟨{ checked.resumeAt finalPc with halted := true }, 2 + returned + 1,
    by omega, (hGuard.trans checkRun).succ (final_step checked), rfl, ?_, ?_⟩
  · simpa [Configuration.resumeAt] using hStatus
  · simpa [Configuration.resumeAt] using hLayout

theorem runs_raw_status (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 9 ∧
      RunsFor program (start beforeInput beforeOutput counter (false :: raw)) target used ∧
      target.halted = true ∧ target.outputTape.current = some
        ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, _⟩ :=
    runs_raw_layout beforeInput beforeOutput width counter raw hCounter
  exact ⟨target, used, hUsed, run, hHalt, hStatus⟩

/-- An incomplete first field remains rejected after the actual stage-tag
guard. No assumption on how many payload bits were present is needed. -/
theorem rejects_incomplete_field (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    (hIncomplete : FiniteBitEncoding.undelimit raw = none) :
    ∃ target used, used ≤ 9 * width + 9 ∧
      RunsFor program (start beforeInput beforeOutput counter (false :: raw)) target used ∧
      target.halted = true ∧ target.outputTape.current = some false := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus⟩ :=
    runs_raw_status beforeInput beforeOutput width counter raw hCounter
  exact ⟨target, used, hUsed, run, hHalt, by simpa [hIncomplete] using hStatus⟩

/-- Acceptance of the first-stage native code entails a complete field,
not merely a correctly sized initial payload prefix. -/
theorem field_of_accepted_run (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    {target : Configuration} {used : Nat}
    (run : RunsFor program (start beforeInput beforeOutput counter (false :: raw)) target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ field tail, FiniteBitEncoding.delimit field ++ tail = raw ∧ field.length = width := by
  obtain ⟨checked, steps, _, checkRun, checkHalt, hStatus⟩ :=
    runs_raw_status beforeInput beforeOutput width counter raw hCounter
  have hSame := run.halted_finish_eq_of_no_randomBit checkRun hHalt checkHalt no_randomBit
  rw [← hSame, hAccept] at hStatus
  cases hParse : FiniteBitEncoding.undelimit raw with
  | none => simp [hParse] at hStatus
  | some pair =>
      rcases pair with ⟨field, tail⟩
      have hLength : field.length = width := by simpa [hParse] using hStatus.symm
      exact ⟨field, tail, FiniteBitEncoding.delimit_append_of_undelimit hParse, hLength⟩

/-- On a canonical choose-tag prefix, the current output cell is exactly
the Boolean fixed-width test, including short and long candidates. -/
theorem runs_width_status (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter field tail : List Bool)
    (hCounter : counter.length = 3 * width) :
    ∃ target used,
      used ≤ 9 * (width + field.length + 1) + 10 ∧
      RunsFor program
        (start beforeInput beforeOutput counter
          (false :: FiniteBitEncoding.delimit field ++ tail))
        target used ∧ target.halted = true ∧
      target.outputTape.current = some (decide (field.length = width)) := by
  let input : Tape :=
    { Tape.ofBits (false :: FiniteBitEncoding.delimit field ++ tail) with
      left := beforeInput }
  let output : Tape := { Tape.ofBits counter with left := beforeOutput }
  have hGuard := guard_accept input output (by
    simp [input, Tape.ofBits])
  have hChecker := DelimitedTripleWidthCheck.runs_width_status
    (some false :: beforeInput) beforeOutput width counter field tail hCounter
  obtain ⟨after, used, hUsed, run, hHalt, hStatus⟩ := hChecker
  have hJoin :
      ({ pc := checkEntry, inputTape := input.moveRight, outputTape := output } :
        Configuration) =
      (DelimitedTripleWidthCheck.start (some false :: beforeInput)
        beforeOutput counter field tail).rebasePc checkEntry := by
    cases field with
    | nil =>
        simp [input, output, DelimitedTripleWidthCheck.start,
          Configuration.rebasePc, checkEntry, Tape.moveRight,
          Tape.ofBits, FiniteBitEncoding.delimit, List.map_append]
    | cons bit rest =>
        simp [input, output, DelimitedTripleWidthCheck.start,
          Configuration.rebasePc, checkEntry, Tape.moveRight,
          Tape.ofBits, FiniteBitEncoding.delimit, List.map_append]
  rw [hJoin] at hGuard
  obtain ⟨returned, hReturned, embedded⟩ :=
    run.withSubroutine_halted guard DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc
      (by change 0 ≤ 15; omega) rfl hHalt
  have checkRun : RunsFor program
      ((DelimitedTripleWidthCheck.start (some false :: beforeInput)
        beforeOutput counter field tail).rebasePc checkEntry)
      (after.resumeAt finalPc) returned := by
    simpa [check_layout, guard, checkEntry] using embedded
  have hStart : start beforeInput beforeOutput counter
      (false :: FiniteBitEncoding.delimit field ++ tail) =
      ({ inputTape := input, outputTape := output } : Configuration) := rfl
  refine ⟨{ after.resumeAt finalPc with halted := true },
    2 + returned + 1, by omega, ?_, rfl, ?_⟩
  · rw [hStart]
    exact (hGuard.trans checkRun).succ (final_step after)
  · simpa [Configuration.resumeAt] using hStatus

/-- Exact tape layout of the successful first-field scan. In particular,
the input head reaches the next field, the instance cells are retained left
of the output head, and the success marker occupies its current cell. -/
theorem runs_matching (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hCounter : counter.length = 3 * field.length) :
    ∃ used,
      RunsFor program
        (start beforeInput beforeOutput counter
          (false :: FiniteBitEncoding.delimit field ++ tail))
        { (DelimitedTripleWidthCheck.finish
            (some false :: beforeInput) beforeOutput counter field tail).resumeAt
            finalPc with halted := true } used := by
  let input : Tape :=
    { Tape.ofBits (false :: FiniteBitEncoding.delimit field ++ tail) with
      left := beforeInput }
  let output : Tape := { Tape.ofBits counter with left := beforeOutput }
  have hGuard := guard_accept input output (by simp [input, Tape.ofBits])
  have hJoin :
      ({ pc := checkEntry, inputTape := input.moveRight, outputTape := output } :
        Configuration) =
      (DelimitedTripleWidthCheck.start (some false :: beforeInput)
        beforeOutput counter field tail).rebasePc checkEntry := by
    cases field with
    | nil =>
        simp [input, output, DelimitedTripleWidthCheck.start,
          Configuration.rebasePc, checkEntry, Tape.moveRight,
          Tape.ofBits, FiniteBitEncoding.delimit]
    | cons bit rest =>
        simp [input, output, DelimitedTripleWidthCheck.start,
          Configuration.rebasePc, checkEntry, Tape.moveRight,
          Tape.ofBits, FiniteBitEncoding.delimit]
  rw [hJoin] at hGuard
  have matching := DelimitedTripleWidthCheck.runs_matching_length
    (some false :: beforeInput) beforeOutput counter field tail hCounter
  obtain ⟨returned, _hReturned, embedded⟩ :=
    matching.withSubroutine_halted guard DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc
      (by change 0 ≤ 15; omega) rfl rfl
  have checkRun : RunsFor program
      ((DelimitedTripleWidthCheck.start (some false :: beforeInput)
        beforeOutput counter field tail).rebasePc checkEntry)
      ((DelimitedTripleWidthCheck.finish
        (some false :: beforeInput) beforeOutput counter field tail).resumeAt finalPc)
      returned := by
    simpa [check_layout, guard, checkEntry] using embedded
  refine ⟨2 + returned + 1, ?_⟩
  change RunsFor program
    ({ inputTape := input, outputTape := output } : Configuration)
    _ _
  exact (hGuard.trans checkRun).succ
    (final_step (DelimitedTripleWidthCheck.finish
      (some false :: beforeInput) beforeOutput counter field tail))

/-- Public tape-layout consequence of a successful scan. The internal
return address is intentionally omitted from this interface. -/
theorem runs_matching_layout (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hCounter : counter.length = 3 * field.length) :
    ∃ target used,
      RunsFor program
        (start beforeInput beforeOutput counter
          (false :: FiniteBitEncoding.delimit field ++ tail))
        target used ∧ target.halted = true ∧
      target.inputTape =
        (DelimitedTripleWidthCheck.finish
          (some false :: beforeInput) beforeOutput counter field tail).inputTape ∧
      target.outputTape =
        (DelimitedTripleWidthCheck.finish
          (some false :: beforeInput) beforeOutput counter field tail).outputTape := by
  obtain ⟨used, run⟩ := runs_matching beforeInput beforeOutput counter field tail hCounter
  exact ⟨_, used, run, rfl, rfl, rfl⟩

/-- A malformed tag is rejected; a false tag invokes the width checker,
which itself stops on arbitrary finite retained tapes. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ target used, used ≤ 9 * (input.right.length + 1) + 12 ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  cases hTag : input.current with
  | none =>
      obtain ⟨target, run, hHalt, _⟩ := guard_reject input output (Or.inl hTag)
      exact ⟨target, 3, by omega, run, hHalt⟩
  | some bit =>
      cases bit with
      | true =>
          obtain ⟨target, run, hHalt, _⟩ :=
            guard_reject input output (Or.inr hTag)
          exact ⟨target, 3, by omega, run, hHalt⟩
      | false =>
          have guardRun := guard_accept input output hTag
          obtain ⟨after, used, hUsed, check, hHalt⟩ :=
            DelimitedTripleWidthCheck.terminates_from_anyTape
              input.moveRight output
          obtain ⟨returned, hReturned, embedded⟩ :=
            check.withSubroutine_halted guard DelimitedTripleWidthCheck.program
              [.halt, .write .output false, .halt] finalPc
              (by change 0 ≤ 15; omega) rfl hHalt
          have checkRun : RunsFor program
              (({ inputTape := input.moveRight, outputTape := output } : Configuration).rebasePc checkEntry)
              (after.resumeAt finalPc) returned := by
            change RunsFor program
              (({ inputTape := input.moveRight, outputTape := output } : Configuration).rebasePc checkEntry)
              (after.resumeAt finalPc) returned at embedded
            exact embedded
          refine ⟨_, 2 + returned + 1, ?_,
            (guardRun.trans checkRun).succ (final_step after), rfl⟩
          cases hRight : input.right <;>
            simp [Tape.moveRight, hRight] at hUsed ⊢ <;> omega

end Machine.ChooseFirstWidthCheck
