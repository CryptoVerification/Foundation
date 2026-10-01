import Foundation.Machine.ContextualInput
import Foundation.Machine.GuardedTrace

namespace Machine

/-- Reach fresh input scratch by scanning three existing blank-separated
blocks. Every scanned cell and crossed separator costs native transitions;
all stored blocks and the other tape are preserved. -/
def seekStoredInputScratch : Program :=
  GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
  GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
  GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ [.halt]

def seekStoredInputScratchStart (before : List (Option Bool))
    (first second third : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  seekBitstringNextStart before first
    (second.map some ++ none :: third.map some ++ none :: List.replicate blanks none) output

def seekStoredInputScratchFinish (before : List (Option Bool))
    (first second third : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  { pc := 18,
    inputTape := {
      left := none :: third.reverse.map some ++ none :: second.reverse.map some ++
        none :: first.reverse.map some ++ before
      right := List.replicate (blanks - 1) none },
    outputTape := output, halted := true }

def seekStoredInputScratchSteps (first second third : List Bool) : Nat :=
  (3 * first.length + 3) + (3 * second.length + 3) + (3 * third.length + 3) + 1

/-- The trace retains the complete finite representation, including any
remaining explicit blank padding after the new scratch head. -/
theorem seekStoredInputScratch_runs (before : List (Option Bool))
    (first second third : List Bool) (blanks : Nat) (output : Tape) :
    RunsFor seekStoredInputScratch (seekStoredInputScratchStart before first second third blanks output)
      (seekStoredInputScratchFinish before first second third blanks output)
      (seekStoredInputScratchSteps first second third) := by
  let beforeSecond := none :: first.reverse.map some ++ before
  let beforeThird := none :: second.reverse.map some ++ beforeSecond
  let tailSecond := third.map some ++ none :: List.replicate blanks none
  let afterFirst := seekBitstringNextFinish before first (second.map some ++ none :: tailSecond) output
  have hFirst := (seekBitstringNext_runs before first (second.map some ++ none :: tailSecond) output).withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput
    (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have hFirst' : RunsFor seekStoredInputScratch
      (seekStoredInputScratchStart before first second third blanks output)
      (afterFirst.resumeAt 6) (3 * first.length + 3) := by
    simpa [seekStoredInputScratch, seekStoredInputScratchStart, tailSecond, afterFirst,
      Program.withSubroutine, Configuration.rebasePc, List.append_assoc] using hFirst
  have hSecondStart : afterFirst.resumeAt 6 =
      (seekBitstringNextStart beforeSecond second tailSecond output).rebasePc 6 := by
    cases second <;> simp [afterFirst, seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      beforeSecond, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hSecondStart] at hFirst'
  have hSecond := (seekBitstringNext_runs beforeSecond second tailSecond output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput
    (GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  let afterSecond := seekBitstringNextFinish beforeSecond second tailSecond output
  change RunsFor seekStoredInputScratch
    ((seekBitstringNextStart beforeSecond second tailSecond output).rebasePc 6)
    (afterSecond.resumeAt 12) (3 * second.length + 3) at hSecond
  have hThirdStart : afterSecond.resumeAt 12 =
      (seekBitstringNextStart beforeThird third (List.replicate blanks none) output).rebasePc 12 := by
    cases third <;> simp [afterSecond, seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      tailSecond, beforeThird, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hThirdStart] at hSecond
  have hThird := (seekBitstringNext_runs beforeThird third (List.replicate blanks none) output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12)
    GuardedCompiler.seekScratchInput [.halt] 18
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have hThirdFinish : seekBitstringNextFinish beforeThird third (List.replicate blanks none) output =
      { seekStoredInputScratchFinish before first second third blanks output with pc := 4 } := by
    cases blanks <;> simp [seekBitstringNextFinish_layout_cells, seekStoredInputScratchFinish,
      beforeThird, beforeSecond, Tape.moveRight, List.append_assoc, List.replicate_succ]
  rw [hThirdFinish] at hThird
  change RunsFor seekStoredInputScratch
    ((seekBitstringNextStart beforeThird third (List.replicate blanks none) output).rebasePc 12)
    ((seekStoredInputScratchFinish before first second third blanks output).resumeAt 18)
    (3 * third.length + 3) at hThird
  have hHalt : Step seekStoredInputScratch
      ((seekStoredInputScratchFinish before first second third blanks output).resumeAt 18)
      (seekStoredInputScratchFinish before first second third blanks output) := by
    simp [Step, successors, next, seekStoredInputScratch, GuardedCompiler.seekScratchInput,
      Program.asSubroutine, Instruction.asSubroutine, seekStoredInputScratchFinish,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((hFirst'.trans hSecond).trans hThird) hHalt

theorem seekStoredInputScratch_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ seekStoredInputScratch := by
  simp [seekStoredInputScratch, GuardedCompiler.seekScratchInput,
    Program.asSubroutine, Instruction.asSubroutine]

theorem seekStoredInputScratch_eval (before : List (Option Bool))
    (first second third : List Bool) (blanks : Nat) (output : Tape) :
    evalConfigWithin seekStoredInputScratch
      (seekStoredInputScratchStart before first second third blanks output)
      (seekStoredInputScratchSteps first second third) =
      PMF.pure (seekStoredInputScratchFinish before first second third blanks output) :=
  (seekStoredInputScratch_runs before first second third blanks output).evalConfigWithin_eq_pure_of_no_randomBit
    seekStoredInputScratch_no_randomBit

theorem seekStoredInputScratch_steps_eq (first second third : List Bool) :
    seekStoredInputScratchSteps first second third = 3 * (first.length + second.length + third.length) + 10 := by
  simp only [seekStoredInputScratchSteps]
  omega

theorem seekStoredInputScratch_control_closed (c d : Configuration)
    (hPc : c.pc < seekStoredInputScratch.length) (step : Step seekStoredInputScratch c d)
    (_hRunning : d.halted = false) : d.pc < seekStoredInputScratch.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 19 at hPc
  change d.pc < 19
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, seekStoredInputScratch,
    GuardedCompiler.seekScratchInput, Program.asSubroutine, Instruction.asSubroutine,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Three native scans stop on every finite input tape and retain the exact
successive input-head positions. The local `advance` expression describes
the proved native scan; it is not an additional machine instruction. -/
theorem seekStoredInputScratch_terminates_with_input_layout (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor seekStoredInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = advance (advance (advance input)) := by
  obtain ⟨first, t₁, h₁, run₁, halt₁, output₁⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape input output
  obtain ⟨second, t₂, h₂, run₂, halt₂, output₂⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape first.inputTape first.outputTape
  obtain ⟨third, t₃, h₃, run₃, halt₃, output₃⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape second.inputTape second.outputTape
  let a := GuardedCompiler.seekScratchInput.asSubroutine 0 6
  let b := GuardedCompiler.seekScratchInput.asSubroutine 6 12
  let k := GuardedCompiler.seekScratchInput.asSubroutine 12 18
  have firstRun := run₁.withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (b ++ k ++ [.halt]) 6
    (by change 0 < 5; decide) rfl halt₁ GuardedCompiler.seekScratchInput_control_closed
  change RunsFor seekStoredInputScratch
    ({ inputTape := input, outputTape := output } : Configuration) (first.resumeAt 6) t₁ at firstRun
  have secondRun := run₂.withSubroutine_halted_of_closed
    a GuardedCompiler.seekScratchInput (k ++ [.halt]) 12
    (by change 0 < 5; decide) rfl halt₂ GuardedCompiler.seekScratchInput_control_closed
  change RunsFor seekStoredInputScratch (first.resumeAt 6) (second.resumeAt 12) t₂ at secondRun
  have thirdRun := run₃.withSubroutine_halted_of_closed
    (a ++ b) GuardedCompiler.seekScratchInput [.halt] 18
    (by change 0 < 5; decide) rfl halt₃ GuardedCompiler.seekScratchInput_control_closed
  change RunsFor seekStoredInputScratch (second.resumeAt 12) (third.resumeAt 18) t₃ at thirdRun
  let finish : Configuration := { third with pc := 18, halted := true }
  have last : Step seekStoredInputScratch (third.resumeAt 18) finish := by
    simp [Step, successors, next, seekStoredInputScratch, GuardedCompiler.seekScratchInput,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, t₁ + t₂ + t₃ + 1, ?_,
    RunsFor.succ ((firstRun.trans secondRun).trans thirdRun) last, rfl,
    output₃.trans (output₂.trans output₁), ?_⟩
  · have storage₁ := GuardedCompiler.sourceStorage_le_of_run run₁
    have storage₂ := GuardedCompiler.sourceStorage_le_of_run run₂
    change first.inputTape.cells + first.outputTape.cells ≤ input.cells + output.cells + t₁ at storage₁
    change second.inputTape.cells + second.outputTape.cells ≤
      first.inputTape.cells + first.outputTape.cells + t₂ at storage₂
    omega
  · have hFirst := (GuardedCompiler.seekScratchInput_halted_input_layout
      input output first t₁ run₁ halt₁).1
    have hSecond := (GuardedCompiler.seekScratchInput_halted_input_layout
      first.inputTape first.outputTape second t₂ run₂ halt₂).1
    have hThird := (GuardedCompiler.seekScratchInput_halted_input_layout
      second.inputTape second.outputTape third t₃ run₃ halt₃).1
    dsimp only [finish]
    rw [hThird, hSecond, hFirst]

/-- Three native scans stop on every finite input tape. Malformed retained
blocks may change which blank is reached; stopping does not assume that the
resulting head is the intended protocol scratch region. Every crossed cell
and the final caller halt are charged, and the other tape is unchanged. -/
theorem seekStoredInputScratch_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor seekStoredInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, hBound, run, hHalted, hOutput, _⟩ :=
    seekStoredInputScratch_terminates_with_input_layout input output
  exact ⟨finish, used, hBound, run, hHalted, hOutput⟩

theorem seekStoredInputScratch_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor seekStoredInputScratch
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (100 * (input.cells + output.cells) + 100)) : finish.halted = true := by
  obtain ⟨target, used, hBound, trace, hHalt, _⟩ := seekStoredInputScratch_terminates_from_anyTape input output
  have hEval := trace.evalConfigWithin_eq_pure_of_no_randomBit seekStoredInputScratch_no_randomBit
  have hAt (c : Configuration) (hc : PaddedRunsFor seekStoredInputScratch
      ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval, PMF.mem_support_pure_iff] at hMem
    simpa only [hMem] using hHalt
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hEval, PMF.mem_support_pure_iff] at hMem
  simpa only [hMem] using hHalt

end Machine
