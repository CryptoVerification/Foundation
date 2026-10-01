import Foundation.Machine.BitstringRewind
import Foundation.Machine.SubroutineProbability
import Foundation.Machine.GuardedTrace

namespace Machine

/-- Restore the earliest of three stored input blocks. Rewind the consumed
part of the canonical response, cross a real blank, rewind the raw reply,
cross its blank, and rewind the DDH input. The other tape, which contains
the selected message and challenge, is untouched by all eighteen instructions. -/
def restoreStoredInput : Program :=
  rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input] ++
    rewindBitstring.asSubroutine 6 11 ++ [.moveLeft .input] ++
    rewindBitstring.asSubroutine 12 17 ++ [.halt]

def restoreStoredInputStart (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := {
      left := consumed.reverse.map some ++ none :: reply.reverse.map some ++
        none :: original.reverse.map some ++ none :: before
      current := current
      right := right },
    outputTape := output }

def restoreStoredInputFinish (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 17,
    inputTape := ({
      left := before
      right := original.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right } : Tape).moveRight,
    outputTape := output, halted := true }

def restoreStoredInputSteps (original reply consumed : List Bool) : Nat :=
  (2 * consumed.length + 4) + 1 + (2 * reply.length + 4) + 1 + (2 * original.length + 4) + 1

/-- Exact native transitions, including all three scans, both separator
crossings, and the final halt. No stored bit is changed or copied for free. -/
theorem restoreStoredInput_runs (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    RunsFor restoreStoredInput (restoreStoredInputStart before original reply consumed current right output)
      (restoreStoredInputFinish before original reply consumed current right output)
      (restoreStoredInputSteps original reply consumed) := by
  let savedOriginal := original.reverse.map some ++ none :: before
  let savedReply := reply.reverse.map some ++ none :: savedOriginal
  let consumedRight := consumed.map some ++ current :: right
  let replyRight := reply.map some ++ none :: consumedRight
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := rewindBitstring.asSubroutine 12 17
  let rewound : Configuration :=
    { pc := 3, inputTape := ({ left := savedReply, right := consumedRight } : Tape).moveRight,
      outputTape := output, halted := true }
  let back : Configuration :=
    { pc := 6, inputTape := { left := savedReply, right := consumedRight }, outputTape := output }
  have hFirst := (rewindScratch_runs_from savedReply consumed current right output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ [.moveLeft .input] ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hFirst' : RunsFor restoreStoredInput
      (restoreStoredInputStart before original reply consumed current right output)
      (rewound.resumeAt 5) (2 * consumed.length + 4) := by
    simpa [restoreStoredInput, Program.withSubroutine, restoreStoredInputStart, savedReply,
      savedOriginal, consumedRight, rewound, b, k, Configuration.rebasePc,
      List.append_assoc] using hFirst
  have hBack : Step restoreStoredInput (rewound.resumeAt 5) back := by
    cases consumed <;> simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, rewound, back, consumedRight,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft]
  let replyRewound : Configuration :=
    { pc := 3, inputTape := ({ left := savedOriginal, right := replyRight } : Tape).moveRight,
      outputTape := output, halted := true }
  let originalBack : Configuration :=
    { pc := 12, inputTape := { left := savedOriginal, right := replyRight }, outputTape := output }
  have hSecond := (rewindScratch_runs_from savedOriginal reply none consumedRight output).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring ([.moveLeft .input] ++ k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor restoreStoredInput back (replyRewound.resumeAt 11) (2 * reply.length + 4) at hSecond
  have hOriginalBack : Step restoreStoredInput (replyRewound.resumeAt 11) originalBack := by
    cases reply <;> simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, replyRewound, originalBack, replyRight,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft]
  have hThird := (rewindScratch_runs_from before original none replyRight output).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b ++ [.moveLeft .input]) rewindBitstring [.halt] 17
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hThird' : RunsFor restoreStoredInput originalBack
    ((restoreStoredInputFinish before original reply consumed current right output).resumeAt 17)
    (2 * original.length + 4) := by
    simpa [restoreStoredInput, Program.withSubroutine, a, b, originalBack, savedOriginal,
      replyRight, consumedRight, restoreStoredInputFinish, Configuration.rebasePc,
      Configuration.resumeAt, Program.asSubroutine_length,
      show rewindBitstring.length = 4 from rfl, List.append_assoc] using hThird
  have hHalt : Step restoreStoredInput
      ((restoreStoredInputFinish before original reply consumed current right output).resumeAt 17)
      (restoreStoredInputFinish before original reply consumed current right output) := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, restoreStoredInputFinish,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (((RunsFor.succ hFirst' hBack).trans hSecond).succ hOriginalBack |>.trans hThird') hHalt

theorem restoreStoredInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ restoreStoredInput := by
  simp [restoreStoredInput, rewindBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem restoreStoredInput_eval (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin restoreStoredInput
      (restoreStoredInputStart before original reply consumed current right output)
      (restoreStoredInputSteps original reply consumed) =
      PMF.pure (restoreStoredInputFinish before original reply consumed current right output) :=
  (restoreStoredInput_runs before original reply consumed current right output).evalConfigWithin_eq_pure_of_no_randomBit
    restoreStoredInput_no_randomBit

theorem restoreStoredInputFinish_output (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    (restoreStoredInputFinish before original reply consumed current right output).outputTape = output := rfl

theorem restoreStoredInput_control_closed (c d : Configuration)
    (hPc : c.pc < restoreStoredInput.length) (step : Step restoreStoredInput c d)
    (_hRunning : d.halted = false) : d.pc < restoreStoredInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 18 at hPc
  change d.pc < 18
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, restoreStoredInput,
    rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- All three native rewinds stop on arbitrary finite tapes. A malformed
separator can change the restored location, but cannot turn any scan into
an infinite traversal. The two separator crossings and caller halt are
actual transitions, and the other physical tape is preserved. -/
theorem restoreStoredInput_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨first, t₁, h₁, run₁, halt₁, output₁⟩ := rewindBitstring_terminates_from input output
  obtain ⟨second, t₂, h₂, run₂, halt₂, output₂⟩ :=
    rewindBitstring_terminates_from first.inputTape.moveLeft first.outputTape
  obtain ⟨third, t₃, h₃, run₃, halt₃, output₃⟩ :=
    rewindBitstring_terminates_from second.inputTape.moveLeft second.outputTape
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := rewindBitstring.asSubroutine 12 17
  have firstRun := run₁.withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ [.moveLeft .input] ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl halt₁ rewindBitstring_control_closed
  change RunsFor restoreStoredInput
    ({ inputTape := input, outputTape := output } : Configuration) (first.resumeAt 5) t₁ at firstRun
  let secondStart : Configuration :=
    { pc := 6, inputTape := first.inputTape.moveLeft, outputTape := first.outputTape }
  have move₁ : Step restoreStoredInput (first.resumeAt 5) secondStart := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, secondStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have secondRun := run₂.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring ([.moveLeft .input] ++ k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl halt₂ rewindBitstring_control_closed
  change RunsFor restoreStoredInput secondStart (second.resumeAt 11) t₂ at secondRun
  let thirdStart : Configuration :=
    { pc := 12, inputTape := second.inputTape.moveLeft, outputTape := second.outputTape }
  have move₂ : Step restoreStoredInput (second.resumeAt 11) thirdStart := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, thirdStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have thirdRun := run₃.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b ++ [.moveLeft .input]) rewindBitstring [.halt] 17
    (by change 0 < 4; decide) rfl halt₃ rewindBitstring_control_closed
  change RunsFor restoreStoredInput thirdStart (third.resumeAt 17) t₃ at thirdRun
  let finish : Configuration := { third with pc := 17, halted := true }
  have last : Step restoreStoredInput (third.resumeAt 17) finish := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, t₁ + 1 + t₂ + 1 + t₃ + 1, ?_,
    RunsFor.succ (((RunsFor.succ firstRun move₁).trans secondRun).succ move₂ |>.trans thirdRun) last,
    rfl, output₃.trans (output₂.trans output₁)⟩
  have storage₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have storage₂ := GuardedCompiler.sourceStorage_le_of_run run₂
  have moved₁ := Tape.cells_moveLeft_le first.inputTape
  have moved₂ := Tape.cells_moveLeft_le second.inputTape
  have left₁ : input.left.length ≤ input.cells := by dsimp only [Tape.cells]; omega
  have left₂ : first.inputTape.moveLeft.left.length ≤ first.inputTape.moveLeft.cells := by
    dsimp only [Tape.cells]; omega
  have left₃ : second.inputTape.moveLeft.left.length ≤ second.inputTape.moveLeft.cells := by
    dsimp only [Tape.cells]; omega
  change first.inputTape.cells + first.outputTape.cells ≤ input.cells + output.cells + t₁ at storage₁
  change second.inputTape.cells + second.outputTape.cells ≤
    first.inputTape.moveLeft.cells + first.outputTape.cells + t₂ at storage₂
  omega

/-- A common padded budget covers every branch of the real restoration
program, independently of a successful stored-input layout. -/
theorem restoreStoredInput_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor restoreStoredInput
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (100 * (input.cells + output.cells) + 100)) : finish.halted = true := by
  obtain ⟨target, used, hBound, trace, hHalted, _⟩ :=
    restoreStoredInput_terminates_from_anyTape input output
  have hEval := trace.evalConfigWithin_eq_pure_of_no_randomBit restoreStoredInput_no_randomBit
  have hAt (c : Configuration) (hc : PaddedRunsFor restoreStoredInput
      ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval, PMF.mem_support_pure_iff] at hMem
    simpa only [hMem] using hHalted
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hEval, PMF.mem_support_pure_iff] at hMem
  simpa only [hMem] using hHalted

end Machine
