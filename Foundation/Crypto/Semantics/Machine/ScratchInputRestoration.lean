import Foundation.Crypto.Semantics.Machine.StoredInputRewind

namespace Machine

/-- Return from an additional scratch copy to an earlier stored original
input. Rewinding the scratch block and crossing its separator are native
steps before invoking the three-block restoration routine. -/
def restoreInputBeforeScratch : Program :=
  rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input] ++
  restoreStoredInput.asSubroutine 6 25 ++ [.halt]

def restoreInputBeforeScratchStart (before : List (Option Bool))
    (original reply canonical scratch : List Bool) (padding : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := {
      left := scratch.reverse.map some ++ none :: canonical.reverse.map some ++ none ::
        reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
      right := padding }, outputTape := output }

def restoreInputBeforeScratchFinish (before : List (Option Bool))
    (original reply canonical scratch : List Bool) (padding : List (Option Bool)) (output : Tape) : Configuration :=
  { restoreStoredInputFinish before original reply canonical none (scratch.map some ++ none :: padding) output
      with pc := 25 }

def restoreInputBeforeScratchSteps (original reply canonical scratch : List Bool) : Nat :=
  (2 * scratch.length + 4) + 1 + restoreStoredInputSteps original reply canonical + 1

theorem restoreInputBeforeScratch_runs (before : List (Option Bool))
    (original reply canonical scratch : List Bool) (padding : List (Option Bool)) (output : Tape) :
    RunsFor restoreInputBeforeScratch
      (restoreInputBeforeScratchStart before original reply canonical scratch padding output)
      (restoreInputBeforeScratchFinish before original reply canonical scratch padding output)
      (restoreInputBeforeScratchSteps original reply canonical scratch) := by
  let saved := canonical.reverse.map some ++ none :: reply.reverse.map some ++ none ::
    original.reverse.map some ++ none :: before
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ left := saved, right := scratch.map some ++ none :: padding } : Tape).moveRight,
      outputTape := output, halted := true }
  have hRewind := (rewindScratch_runs_from saved scratch none padding output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ restoreStoredInput.asSubroutine 6 25 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hRewind' : RunsFor restoreInputBeforeScratch
      (restoreInputBeforeScratchStart before original reply canonical scratch padding output)
      (rewound.resumeAt 5) (2 * scratch.length + 4) := by
    simpa [restoreInputBeforeScratch, Program.withSubroutine, restoreInputBeforeScratchStart,
      rewound, saved, Configuration.rebasePc, List.append_assoc] using hRewind
  let restoreStart := restoreStoredInputStart before original reply canonical none
    (scratch.map some ++ none :: padding) output
  have hBack : Step restoreInputBeforeScratch (rewound.resumeAt 5) (restoreStart.rebasePc 6) := by
    cases scratch <;> simp [Step, successors, next, restoreInputBeforeScratch, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, rewound, restoreStart, restoreStoredInputStart,
      saved, Configuration.resumeAt, Configuration.rebasePc, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.moveLeft, List.append_assoc]
  have hRestore := (restoreStoredInput_runs before original reply canonical none
      (scratch.map some ++ none :: padding) output).withSubroutine_halted_of_closed
    (rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input]) restoreStoredInput [.halt] 25
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor restoreInputBeforeScratch (restoreStart.rebasePc 6)
    ((restoreInputBeforeScratchFinish before original reply canonical scratch padding output).resumeAt 25)
    (restoreStoredInputSteps original reply canonical) at hRestore
  have hHalt : Step restoreInputBeforeScratch
      ((restoreInputBeforeScratchFinish before original reply canonical scratch padding output).resumeAt 25)
      (restoreInputBeforeScratchFinish before original reply canonical scratch padding output) := by
    simp [Step, successors, next, restoreInputBeforeScratch, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, restoreInputBeforeScratchFinish,
      restoreStoredInputFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((RunsFor.succ hRewind' hBack).trans hRestore) hHalt

theorem restoreInputBeforeScratch_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ restoreInputBeforeScratch := by
  simp [restoreInputBeforeScratch, restoreStoredInput, rewindBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem restoreInputBeforeScratch_eval (before : List (Option Bool))
    (original reply canonical scratch : List Bool) (padding : List (Option Bool)) (output : Tape) :
    evalConfigWithin restoreInputBeforeScratch
      (restoreInputBeforeScratchStart before original reply canonical scratch padding output)
      (restoreInputBeforeScratchSteps original reply canonical scratch) =
      PMF.pure (restoreInputBeforeScratchFinish before original reply canonical scratch padding output) :=
  (restoreInputBeforeScratch_runs before original reply canonical scratch padding output).evalConfigWithin_eq_pure_of_no_randomBit
    restoreInputBeforeScratch_no_randomBit

theorem restoreInputBeforeScratch_steps_eq (original reply canonical scratch : List Bool) :
    restoreInputBeforeScratchSteps original reply canonical scratch =
      2 * (original.length + reply.length + canonical.length + scratch.length) + 21 := by
  simp only [restoreInputBeforeScratchSteps, restoreStoredInputSteps]
  omega

theorem restoreInputBeforeScratch_control_closed (c d : Configuration)
    (hPc : c.pc < restoreInputBeforeScratch.length) (step : Step restoreInputBeforeScratch c d)
    (_hRunning : d.halted = false) : d.pc < restoreInputBeforeScratch.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 26 at hPc
  change d.pc < 26
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, restoreInputBeforeScratch,
    restoreStoredInput, rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Restoring the original input from an additional scratch region stops
on arbitrary finite tapes. The rewind and blank crossing remain actual
instructions even when the stored block boundaries are malformed. -/
theorem restoreInputBeforeScratch_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000 * (input.cells + output.cells) + 1000 ∧
      RunsFor restoreInputBeforeScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨rewound, rewindTime, hRewindTime, rewindRun, rewindHalt, rewindOutput⟩ :=
    rewindBitstring_terminates_from input output
  let restoreStart : Configuration :=
    { pc := 6, inputTape := rewound.inputTape.moveLeft, outputTape := rewound.outputTape }
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreStoredInput_terminates_from_anyTape restoreStart.inputTape restoreStart.outputTape
  have hRewind := rewindRun.withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ restoreStoredInput.asSubroutine 6 25 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rewindHalt rewindBitstring_control_closed
  change RunsFor restoreInputBeforeScratch
    ({ inputTape := input, outputTape := output } : Configuration) (rewound.resumeAt 5) rewindTime at hRewind
  have hMove : Step restoreInputBeforeScratch (rewound.resumeAt 5) restoreStart := by
    have code : restoreInputBeforeScratch[5]? = some (.moveLeft .input) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, restoreStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have toRestore := RunsFor.succ hRewind hMove
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    (rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input]) restoreStoredInput [.halt] 25
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor restoreInputBeforeScratch restoreStart (restored.resumeAt 25) restoreTime at hRestore
  let finish : Configuration := { restored with pc := 25, halted := true }
  have last : Step restoreInputBeforeScratch (restored.resumeAt 25) finish := by
    have code : restoreInputBeforeScratch[25]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, rewindTime + 1 + restoreTime + 1, ?_,
    RunsFor.succ (toRestore.trans hRestore) last, rfl, restoreOutput.trans rewindOutput⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run toRestore
  change restoreStart.inputTape.cells + restoreStart.outputTape.cells ≤ input.cells + output.cells + (rewindTime + 1) at hStorage
  have hLeft : input.left.length ≤ input.cells := by dsimp only [Tape.cells]; omega
  omega

end Machine
