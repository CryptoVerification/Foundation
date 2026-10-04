import Foundation.Machine.ChooseFirstWidthCheck
import Foundation.Machine.BitstringRewind
import Foundation.Machine.TapeSwap
import Foundation.Machine.GuardedTrace

namespace Machine.ChooseSecondWidthCheck

private def rewindEntry : Nat := 2
private def checkEntry : Nat := rewindEntry + rewindBitstring.length + 1
private def finalPc : Nat := checkEntry + DelimitedTripleWidthCheck.program.length + 1
private def rejectPc : Nat := finalPc + 1

private def guard : Program :=
  [.branch .output rejectPc rejectPc 1, .erase .output]

/-- Require the preceding first-field status, clear it, physically rewind
the three-field instance counter, and check the next delimited field. -/
def program : Program :=
  guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry ++
    DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
      [.halt, .write .output false, .halt]

private theorem rewind_layout : program =
    Program.withSubroutine guard rewindBitstring.swapTapes
      (DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
        [.halt, .write .output false, .halt]) checkEntry := by
  simp [program, Program.withSubroutine, guard, rewindEntry]

private theorem check_layout : program =
    Program.withSubroutine
      (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry)
      DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc := by
  simp [program, Program.withSubroutine, guard, rewindEntry, checkEntry,
    Program.asSubroutine_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalPc)
      { c.resumeAt finalPc with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

private theorem guard_accept (input output : Tape)
    (hStatus : output.current = some true) :
    RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
        rewindEntry) 2 := by
  let source : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { source with pc := 1 }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, guard, source, selected,
      Instruction.next, Configuration.tape, hStatus]
  have h1 : Step program selected
      (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
        rewindEntry) := by
    simp [Step, successors, next, program, guard, source, selected,
      rewindEntry, Instruction.next, Configuration.updateTape,
      Configuration.advance, Configuration.rebasePc]
  exact ((RunsFor.zero _).succ h0).succ h1

private theorem guard_reject_layout (input output : Tape)
    (hStatus : output.current = none ∨ output.current = some false) :
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
    rcases hStatus with hBlank | hFalse
    · simp [Step, successors, next, program, guard, source, selected,
        Instruction.next, Configuration.tape, hBlank]
    · simp [Step, successors, next, program, guard, source, selected,
        Instruction.next, Configuration.tape, hFalse]
  have h1 : Step program selected written := by
    have hLookup : program[rejectPc]? = some (.write .output false) := by native_decide
    simp [Step, successors, next, source, selected, written, hLookup,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step program written { written with halted := true } := by
    have hLookup : program[rejectPc + 1]? = some .halt := by native_decide
    simp [Step, successors, next, written, hLookup, Instruction.next]
  exact ⟨_, (((RunsFor.zero _).succ h0).succ h1).succ h2, rfl,
    by simp [written, Tape.write], rfl⟩

private theorem guard_reject (input output : Tape)
    (h : output.current = none ∨ output.current = some false) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧ target.outputTape.current = some false := by
  obtain ⟨target, run, hHalt, hStatus, _⟩ := guard_reject_layout input output h
  exact ⟨target, run, hHalt, hStatus⟩

/-- A failed first-field status is terminal. The second field is not
mistakenly accepted after an earlier rejection. -/
theorem rejects_failed_first (input output : Tape)
    (hStatus : output.current = some false) :
    ∃ target,
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target 3 ∧ target.halted = true ∧
      target.outputTape.current = some false :=
  guard_reject input output (Or.inr hStatus)

/-- The second-stage guard retains the actual rejected workspace layout. -/
theorem rejects_failed_first_layout (input output : Tape)
    (hStatus : output.current = some false) :
    ∃ target, RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration)
      target 3 ∧ target.halted = true ∧ target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) :=
  guard_reject_layout input output (Or.inr hStatus)

/-- The successful first width scan leaves the second delimiter under the
input head and the instance counter immediately left of its true status. -/
theorem runs_second_raw_layout (beforeInput : List (Option Bool))
    (width : Nat) (counter first raw : List Bool)
    (hCounter : counter.length = 3 * width) :
    let firstFinish := DelimitedTripleWidthCheck.finish
      (some false :: beforeInput) [none] counter first
      raw
    ∃ target used,
      RunsFor program
        ({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape.Equivalent
          { left := consumed.reverse.map some ++ [none],
            current := target.outputTape.current, right := (Tape.ofBits suffix).right } := by
  dsimp only
  let firstFinish := DelimitedTripleWidthCheck.finish
    (some false :: beforeInput) [none] counter first
    raw
  let input := firstFinish.inputTape
  let output := firstFinish.outputTape
  have hOutput : output =
      ⟨counter.reverse.map some ++ [none], some true, []⟩ := rfl
  have hGuard := guard_accept input output (by simp [hOutput])
  have rew := (rewindScratch_runs [] counter input).swapTapes
  have hJoin :
      (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
        rewindEntry) =
      ((rewindScratchStart [] counter input).swapTapes).rebasePc rewindEntry := by
    dsimp [Configuration.swapTapes, Configuration.rebasePc,
      rewindScratchStart]
    rw [hOutput]
    rfl
  rw [hJoin] at hGuard
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    rew.withSubroutine_halted guard rewindBitstring.swapTapes
      (DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
        [.halt, .write .output false, .halt]) checkEntry
      (by change 0 ≤ 4; omega) rfl rfl
  have rewindRun : RunsFor program
      (((rewindScratchStart [] counter input).swapTapes).rebasePc rewindEntry)
      (((rewindScratchFinish [] counter input).swapTapes).resumeAt checkEntry)
      returned₁ := by
    simpa [rewind_layout, guard, rewindEntry] using embedded₁
  let beforeSecond : List (Option Bool) :=
    (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: beforeInput
  let expected : Configuration :=
    { inputTape := { Tape.ofBits raw with left := beforeSecond },
      outputTape := { Tape.ofBits counter with left := [none] } }
  let afterRewind := (rewindScratchFinish [] counter input).swapTapes
  have hEquivalent : (expected.rebasePc checkEntry).Equivalent
      (afterRewind.resumeAt checkEntry) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected,
        beforeSecond, firstFinish, input, DelimitedTripleWidthCheck.finish,
        afterRewind, Configuration.swapTapes, rewindScratchFinish,
        Configuration.rebasePc, Configuration.resumeAt] using
        (Tape.Equivalent.refl ({ Tape.ofBits
          raw with
          left := beforeSecond } : Tape))
    · have hRew := rewindScratchFinish_input_equivalent [] counter input
      simpa [expected,
        Configuration.rebasePc, Configuration.resumeAt,
        afterRewind, Configuration.swapTapes,
        rewindScratchFinish] using hRew.symm
  obtain ⟨finish, used₂, _hUsed₂, checkRun, hHalt₂, hStatus₂, hLayout₂⟩ :=
    DelimitedTripleWidthCheck.runs_raw_decision_layout beforeSecond [none]
      width counter raw hCounter
  have hExpected : expected =
      ({ inputTape := { Tape.ofBits raw with left := beforeSecond },
         outputTape := { Tape.ofBits counter with left := [none] } } : Configuration) := rfl
  rw [← hExpected] at checkRun
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    checkRun.withSubroutine_halted
      (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry)
      DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc
      (Nat.zero_le _) rfl hHalt₂
  have checkEmbedded : RunsFor program (expected.rebasePc checkEntry)
      (finish.resumeAt finalPc) returned₂ := by
    have hEntry :
        (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry).length =
          checkEntry := by
      simp [guard, rewindEntry, checkEntry, Program.asSubroutine_length]
      omega
    simpa only [← check_layout, hEntry] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    checkEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalPc := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalPc]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true },
    2 + (returned₁ + returned₂) + 1, ?_, rfl, ?_, ?_⟩
  · change RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration) _ _
    exact (hGuard.trans (rewindRun.trans actualRun)).succ hLast
  · exact (hActual.2.2.2.1.symm).trans (by
      simpa [Configuration.resumeAt] using hStatus₂)
  · obtain ⟨consumed, suffix, hParts, hTape⟩ := hLayout₂
    refine ⟨consumed, suffix, hParts, ?_⟩
    have eqTape : actual.outputTape.Equivalent finish.outputTape := by
      simpa [Configuration.resumeAt] using hActual.2.2.2.symm
    have eqCurrent : finish.outputTape.current = actual.outputTape.current := by
      simpa [Configuration.resumeAt] using hActual.2.2.2.1
    rw [hTape] at eqTape
    simpa only [eqCurrent] using eqTape

theorem runs_second_raw_status (beforeInput : List (Option Bool))
    (width : Nat) (counter first raw : List Bool)
    (hCounter : counter.length = 3 * width) :
    let firstFinish := DelimitedTripleWidthCheck.finish
      (some false :: beforeInput) [none] counter first
      raw
    ∃ target used,
      RunsFor program
        ({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) := by
  obtain ⟨target, used, run, hHalt, hStatus, _⟩ :=
    runs_second_raw_layout beforeInput width counter first raw hCounter
  exact ⟨target, used, run, hHalt, hStatus⟩

/-- Canonical-field projection of the complete raw second-field check. -/
theorem runs_second_status (beforeInput : List (Option Bool))
    (width : Nat) (counter first second tail : List Bool)
    (hCounter : counter.length = 3 * width) :
    let firstFinish := DelimitedTripleWidthCheck.finish
      (some false :: beforeInput) [none] counter first
      (FiniteBitEncoding.delimit second ++ tail)
    ∃ target used,
      RunsFor program
        ({ inputTape := firstFinish.inputTape, outputTape := firstFinish.outputTape } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some (decide (second.length = width)) := by
  simpa using runs_second_raw_status beforeInput width counter first
    (FiniteBitEncoding.delimit second ++ tail) hCounter

/-- When the second payload has the required width, the scan retains the
exact second-field suffix on the input tape and the consumed instance code
to the left of the output status. This layout is needed by later native
validity checks; the status bit alone does not locate either tape head. -/
theorem runs_second_matching_layout (beforeInput : List (Option Bool))
    (counter first second tail : List Bool)
    (hCounter : counter.length = 3 * second.length) :
    let firstFinish := DelimitedTripleWidthCheck.finish
      (some false :: beforeInput) [none] counter first
      (FiniteBitEncoding.delimit second ++ tail)
    let beforeSecond := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: beforeInput
    let secondFinish := DelimitedTripleWidthCheck.finish
      beforeSecond [none] counter second tail
    ∃ target used,
      RunsFor program
        ({ inputTape := firstFinish.inputTape,
           outputTape := firstFinish.outputTape } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent secondFinish.inputTape ∧
      target.outputTape.Equivalent secondFinish.outputTape := by
  dsimp only
  let firstFinish := DelimitedTripleWidthCheck.finish
    (some false :: beforeInput) [none] counter first
    (FiniteBitEncoding.delimit second ++ tail)
  let beforeSecond := (FiniteBitEncoding.delimit first).reverse.map some ++
    some false :: beforeInput
  let secondFinish := DelimitedTripleWidthCheck.finish
    beforeSecond [none] counter second tail
  let input := firstFinish.inputTape
  let output := firstFinish.outputTape
  have hOutput : output =
      ⟨counter.reverse.map some ++ [none], some true, []⟩ := rfl
  have hGuard := guard_accept input output (by simp [hOutput])
  have rew := (rewindScratch_runs [] counter input).swapTapes
  have hJoin :
      (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
        rewindEntry) =
      ((rewindScratchStart [] counter input).swapTapes).rebasePc rewindEntry := by
    dsimp [Configuration.swapTapes, Configuration.rebasePc,
      rewindScratchStart]
    rw [hOutput]
    rfl
  rw [hJoin] at hGuard
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    rew.withSubroutine_halted guard rewindBitstring.swapTapes
      (DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
        [.halt, .write .output false, .halt]) checkEntry
      (by change 0 ≤ 4; omega) rfl rfl
  have rewindRun : RunsFor program
      (((rewindScratchStart [] counter input).swapTapes).rebasePc rewindEntry)
      (((rewindScratchFinish [] counter input).swapTapes).resumeAt checkEntry)
      returned₁ := by
    simpa [rewind_layout, guard, rewindEntry] using embedded₁
  let expected := DelimitedTripleWidthCheck.start beforeSecond [none]
    counter second tail
  let afterRewind := (rewindScratchFinish [] counter input).swapTapes
  have hEquivalent : (expected.rebasePc checkEntry).Equivalent
      (afterRewind.resumeAt checkEntry) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected, DelimitedTripleWidthCheck.start,
        beforeSecond, firstFinish, input, DelimitedTripleWidthCheck.finish,
        afterRewind, Configuration.swapTapes, rewindScratchFinish,
        Configuration.rebasePc, Configuration.resumeAt] using
        (Tape.Equivalent.refl ({ Tape.ofBits
          (FiniteBitEncoding.delimit second ++ tail) with
          left := beforeSecond } : Tape))
    · have hRew := rewindScratchFinish_input_equivalent [] counter input
      simpa [expected, DelimitedTripleWidthCheck.start,
        Configuration.rebasePc, Configuration.resumeAt,
        afterRewind, Configuration.swapTapes,
        rewindScratchFinish] using hRew.symm
  have checkRun := DelimitedTripleWidthCheck.runs_matching_length
    beforeSecond [none] counter second tail hCounter
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    checkRun.withSubroutine_halted
      (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry)
      DelimitedTripleWidthCheck.program
      [.halt, .write .output false, .halt] finalPc
      (Nat.zero_le _) rfl rfl
  have checkEmbedded : RunsFor program (expected.rebasePc checkEntry)
      (secondFinish.resumeAt finalPc) returned₂ := by
    have hEntry :
        (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry).length =
          checkEntry := by
      simp [guard, rewindEntry, checkEntry, Program.asSubroutine_length]
      omega
    simpa only [← check_layout, hEntry, expected, secondFinish] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    checkEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalPc := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalPc]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true },
    2 + (returned₁ + returned₂) + 1, ?_, rfl, ?_, ?_⟩
  · change RunsFor program
      ({ inputTape := input, outputTape := output } : Configuration) _ _
    exact (hGuard.trans (rewindRun.trans actualRun)).succ hLast
  · exact hActual.2.2.1.symm
  · exact hActual.2.2.2.symm

/-- On any retained tapes the status guard, rewind, and second delimiter
scan all stop. This does not assume either element is well formed. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ target used, used ≤ 100 * (input.cells + output.cells + 1) + 100 ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  cases hStatus : output.current with
  | none =>
      obtain ⟨target, run, hHalt, _⟩ := guard_reject input output (Or.inl hStatus)
      exact ⟨target, 3, by omega, run, hHalt⟩
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨target, run, hHalt, _⟩ :=
            guard_reject input output (Or.inr hStatus)
          exact ⟨target, 3, by omega, run, hHalt⟩
      | true =>
          have guardRun := guard_accept input output hStatus
          obtain ⟨rewound, used₁, hUsed₁, rew, hRewHalt, hRewInput⟩ :=
            rewindBitstring_terminates_from (output.write none) input
          have rewSwapped := rew.swapTapes
          obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
            rewSwapped.withSubroutine_halted guard rewindBitstring.swapTapes
              (DelimitedTripleWidthCheck.program.asSubroutine checkEntry finalPc ++
                [.halt, .write .output false, .halt]) checkEntry
              (by change 0 ≤ 4; omega) rfl hRewHalt
          have rewindRun : RunsFor program
              (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
                rewindEntry)
              (rewound.swapTapes.resumeAt checkEntry) returned₁ := by
            change RunsFor program
              (({ inputTape := input, outputTape := output.write none } : Configuration).rebasePc
                rewindEntry)
              (rewound.swapTapes.resumeAt checkEntry) returned₁ at embedded₁
            exact embedded₁
          obtain ⟨finish, used₂, hUsed₂, checkRun, hCheckHalt⟩ :=
            DelimitedTripleWidthCheck.terminates_from_anyTape
              rewound.swapTapes.inputTape rewound.swapTapes.outputTape
          obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
            checkRun.withSubroutine_halted
              (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry)
              DelimitedTripleWidthCheck.program
              [.halt, .write .output false, .halt] finalPc
              (by change 0 ≤ 15; omega) rfl hCheckHalt
          have checkEmbedded : RunsFor program
              (rewound.swapTapes.resumeAt checkEntry)
              (finish.resumeAt finalPc) returned₂ := by
            have hEntry :
                (guard ++ rewindBitstring.swapTapes.asSubroutine rewindEntry checkEntry).length =
                  checkEntry := by
              simp [guard, rewindEntry, checkEntry, Program.asSubroutine_length]
              omega
            rw [hEntry] at embedded₂
            change RunsFor program (rewound.swapTapes.resumeAt checkEntry)
              (finish.resumeAt finalPc) returned₂ at embedded₂
            exact embedded₂
          have hCells : rewound.swapTapes.inputTape.right.length = input.right.length := by
            simpa [Configuration.swapTapes] using
              congrArg List.length (congrArg Tape.right hRewInput)
          have hBound :
              2 + returned₁ + returned₂ + 1 ≤
                100 * (input.cells + output.cells + 1) + 100 := by
            rw [hCells] at hUsed₂
            simp only [Tape.write] at hUsed₁
            dsimp only [Tape.cells] at *
            omega
          refine ⟨{ finish.resumeAt finalPc with halted := true },
            2 + returned₁ + returned₂ + 1,
            hBound, ?_, rfl⟩
          change RunsFor program
            ({ inputTape := input, outputTape := output } : Configuration) _ _
          simpa only [Nat.add_assoc] using
            ((guardRun.trans (rewindRun.trans checkEmbedded)).succ
              (final_step finish))

end Machine.ChooseSecondWidthCheck
