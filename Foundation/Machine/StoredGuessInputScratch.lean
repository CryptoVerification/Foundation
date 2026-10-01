import Foundation.Machine.StoredInputScratch

namespace Machine

/-- Reach scratch beyond all five retained blocks. The first two scans
preserve the DDH input and raw reply; the existing three-block scan preserves
the canonical response, selected message and returned product. -/
def seekGuessInputScratch : Program :=
  GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
    GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
    seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]

def seekGuessInputScratchStart (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  seekBitstringNextStart before first
    (second.map some ++ none :: third.map some ++ none :: fourth.map some ++ none ::
      fifth.map some ++ none :: List.replicate blanks none) output

def seekGuessInputScratchFinish (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  { seekStoredInputScratchFinish
      (none :: second.reverse.map some ++ none :: first.reverse.map some ++ before)
      third fourth fifth blanks output with pc := 32 }

def seekGuessInputScratchSteps (first second third fourth fifth : List Bool) : Nat :=
  (3*first.length + 3) + (3*second.length + 3) +
    seekStoredInputScratchSteps third fourth fifth + 1

theorem seekGuessInputScratch_runs (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) :
    RunsFor seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output)
      (seekGuessInputScratchSteps first second third fourth fifth) := by
  let beforeSecond := none :: first.reverse.map some ++ before
  let beforeThird := none :: second.reverse.map some ++ beforeSecond
  let following := third.map some ++ none :: fourth.map some ++ none ::
    fifth.map some ++ none :: List.replicate blanks none
  let afterFirst := seekBitstringNextFinish before first (second.map some ++ none :: following) output
  have hFirst := (seekBitstringNext_runs before first (second.map some ++ none :: following) output).withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have hFirst' : RunsFor seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (afterFirst.resumeAt 6) (3*first.length + 3) := by
    simpa [seekGuessInputScratch, seekGuessInputScratchStart, following, afterFirst,
      Program.withSubroutine, Configuration.rebasePc, List.append_assoc] using hFirst
  have hSecondStart : afterFirst.resumeAt 6 =
      (seekBitstringNextStart beforeSecond second following output).rebasePc 6 := by
    cases second <;> simp [afterFirst, seekBitstringNextFinish_layout_cells,
      seekBitstringNextStart_layout, beforeSecond, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight]
  rw [hSecondStart] at hFirst'
  have hSecond := (seekBitstringNext_runs beforeSecond second following output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput
    (seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  let afterSecond := seekBitstringNextFinish beforeSecond second following output
  change RunsFor seekGuessInputScratch
    ((seekBitstringNextStart beforeSecond second following output).rebasePc 6)
    (afterSecond.resumeAt 12) (3*second.length + 3) at hSecond
  have hThirdStart : afterSecond.resumeAt 12 =
      (seekStoredInputScratchStart beforeThird third fourth fifth blanks output).rebasePc 12 := by
    cases third <;> simp [afterSecond, seekBitstringNextFinish_layout_cells,
      seekStoredInputScratchStart, seekBitstringNextStart_layout, beforeThird, following,
      Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hThirdStart] at hSecond
  have hThird := (seekStoredInputScratch_runs beforeThird third fourth fifth blanks output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12)
    seekStoredInputScratch [.halt] 32
    (by change 0 < 19; decide) rfl rfl seekStoredInputScratch_control_closed
  change RunsFor seekGuessInputScratch
    ((seekStoredInputScratchStart beforeThird third fourth fifth blanks output).rebasePc 12)
    ((seekStoredInputScratchFinish beforeThird third fourth fifth blanks output).resumeAt 32)
    (seekStoredInputScratchSteps third fourth fifth) at hThird
  have hFinish : (seekStoredInputScratchFinish beforeThird third fourth fifth blanks output).resumeAt 32 =
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output).resumeAt 32 := by
    simp [seekGuessInputScratchFinish, beforeThird, beforeSecond, Configuration.resumeAt,
      List.append_assoc]
  rw [hFinish] at hThird
  have hLength : (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32).length = 32 := by
    simp only [List.length_append, Program.asSubroutine_length,
      show GuardedCompiler.seekScratchInput.length = 5 from rfl,
      show seekStoredInputScratch.length = 19 from rfl]
  have hInstruction : seekGuessInputScratch[32]? = some Instruction.halt := by
    change (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32 ++ [Instruction.halt])[32]? = _
    rw [List.getElem?_append_right (by rw [hLength]), hLength]
    rfl
  have hHalt : Step seekGuessInputScratch
      ((seekGuessInputScratchFinish before first second third fourth fifth blanks output).resumeAt 32)
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output) := by
    simp [Step, successors, next, hInstruction, seekGuessInputScratchFinish,
      seekStoredInputScratchFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((hFirst'.trans hSecond).trans hThird) hHalt

theorem seekGuessInputScratch_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ seekGuessInputScratch := by
  simp [seekGuessInputScratch, seekStoredInputScratch, GuardedCompiler.seekScratchInput,
    Program.asSubroutine, Instruction.asSubroutine]

theorem seekGuessInputScratch_eval (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) :
    evalConfigWithin seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (seekGuessInputScratchSteps first second third fourth fifth) =
      PMF.pure (seekGuessInputScratchFinish before first second third fourth fifth blanks output) :=
  (seekGuessInputScratch_runs _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit seekGuessInputScratch_no_randomBit

theorem seekGuessInputScratch_steps_eq (first second third fourth fifth : List Bool) :
    seekGuessInputScratchSteps first second third fourth fifth =
      3*(first.length + second.length + third.length + fourth.length + fifth.length) + 17 := by
  rw [seekGuessInputScratchSteps, seekStoredInputScratch_steps_eq]
  omega

set_option maxHeartbeats 1000000 in
theorem seekGuessInputScratch_control_closed (c d : Configuration)
    (hPc : c.pc < seekGuessInputScratch.length) (step : Step seekGuessInputScratch c d)
    (_hRunning : d.halted = false) : d.pc < seekGuessInputScratch.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 33 at hPc
  change d.pc < 33
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, seekGuessInputScratch,
    seekStoredInputScratch, GuardedCompiler.seekScratchInput, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
