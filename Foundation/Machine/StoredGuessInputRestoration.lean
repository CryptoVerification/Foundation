import Foundation.Machine.StoredInputRewind

namespace Machine

/-- Rewind the five retained blocks after constructing the raw guess body.
The first three-block rewind reaches the canonical response; the next
three-block rewind includes an empty consumed prefix before the raw reply
and DDH input. Each crossing of a separator is charged.
The completed raw body on the other tape is untouched. -/
def restoreGuessInput : Program :=
  restoreStoredInput.asSubroutine 0 19 ++
    restoreStoredInput.asSubroutine 19 38 ++ [.halt]

def restoreGuessInputStart (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  restoreStoredInputStart
    (second.reverse.map some ++ none :: first.reverse.map some ++ none :: before)
    third fourth fifth current right output

def restoreGuessInputFinish (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 38,
    inputTape := ({
      left := before
      right := first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ current :: right } : Tape).moveRight,
    outputTape := output, halted := true }

def restoreGuessInputSteps (first second third fourth fifth : List Bool) : Nat :=
  restoreStoredInputSteps third fourth fifth + restoreStoredInputSteps first second [] + 1

theorem restoreGuessInput_runs (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    RunsFor restoreGuessInput
      (restoreGuessInputStart before first second third fourth fifth current right output)
      (restoreGuessInputFinish before first second third fourth fifth current right output)
      (restoreGuessInputSteps first second third fourth fifth) := by
  let saved := second.reverse.map some ++ none :: first.reverse.map some ++ none :: before
  let following := third.map some ++ none :: fourth.map some ++ none :: fifth.map some ++ current :: right
  let firstFinish := restoreStoredInputFinish saved third fourth fifth current right output
  let atThird : Tape := ({ right := following } : Tape).moveRight
  let secondStart := restoreStoredInputStart before first second [] atThird.current atThird.right output
  have hFirst := (restoreStoredInput_runs saved third fourth fifth current right output).withSubroutine_halted_of_closed
    [] restoreStoredInput (restoreStoredInput.asSubroutine 19 38 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor restoreGuessInput
    (restoreGuessInputStart before first second third fourth fifth current right output)
    (firstFinish.resumeAt 19) (restoreStoredInputSteps third fourth fifth) at hFirst
  have hNext : firstFinish.resumeAt 19 = secondStart.rebasePc 19 := by
    cases third <;> simp [firstFinish, restoreStoredInputFinish, secondStart,
      restoreStoredInputStart, atThird, saved, following, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight, List.append_assoc]
  rw [hNext] at hFirst
  have hSecond := (restoreStoredInput_runs before first second [] atThird.current atThird.right output).withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) restoreStoredInput [.halt] 38
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor restoreGuessInput (secondStart.rebasePc 19)
    ((restoreStoredInputFinish before first second [] atThird.current atThird.right output).resumeAt 38)
    (restoreStoredInputSteps first second []) at hSecond
  have hFinish : (restoreStoredInputFinish before first second [] atThird.current atThird.right output).resumeAt 38 =
      (restoreGuessInputFinish before first second third fourth fifth current right output).resumeAt 38 := by
    cases third <;> simp [restoreStoredInputFinish, restoreGuessInputFinish, atThird, following, Tape.moveRight, Configuration.resumeAt,
      List.append_assoc]
  rw [hFinish] at hSecond
  have hHalt : Step restoreGuessInput
      ((restoreGuessInputFinish before first second third fourth fifth current right output).resumeAt 38)
      (restoreGuessInputFinish before first second third fourth fifth current right output) := by
    simp [Step, successors, next, restoreGuessInput, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, restoreGuessInputFinish,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (hFirst.trans hSecond) hHalt

theorem restoreGuessInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ restoreGuessInput := by
  simp [restoreGuessInput, restoreStoredInput, rewindBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem restoreGuessInput_eval (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin restoreGuessInput
      (restoreGuessInputStart before first second third fourth fifth current right output)
      (restoreGuessInputSteps first second third fourth fifth) =
      PMF.pure (restoreGuessInputFinish before first second third fourth fifth current right output) :=
  (restoreGuessInput_runs _ _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit restoreGuessInput_no_randomBit

theorem restoreGuessInput_steps_eq (first second third fourth fifth : List Bool) :
    restoreGuessInputSteps first second third fourth fifth =
      2 * (first.length + second.length + third.length + fourth.length + fifth.length) + 31 := by
  simp only [restoreGuessInputSteps, restoreStoredInputSteps, List.length_nil]
  omega

set_option maxHeartbeats 1000000 in
theorem restoreGuessInput_control_closed (c d : Configuration)
    (hPc : c.pc < restoreGuessInput.length) (step : Step restoreGuessInput c d)
    (_hRunning : d.halted = false) : d.pc < restoreGuessInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 39 at hPc
  change d.pc < 39
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, restoreGuessInput,
    restoreStoredInput, rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
