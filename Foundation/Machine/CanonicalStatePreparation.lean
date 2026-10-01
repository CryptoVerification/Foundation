import Foundation.Machine.DelimitedSkip
import Foundation.Machine.MessageSelectionPreparation

namespace Machine

/-- Locate the source adversary's retained state in a canonical choose
response. Skip the success tag and both delimited message fields using native
head moves. The state and all cells after it remain unchanged for the guess
request construction, and the other tape is preserved exactly. -/
def prepareCanonicalState : Program :=
  [.moveRight .input] ++ skipDelimited.asSubroutine 1 9 ++
    skipDelimited.asSubroutine 9 17 ++ [.halt]

def prepareCanonicalStateStart (before tail : List (Option Bool))
    (first second state : List Bool) (output : Tape) : Configuration :=
  { inputTape := {
      left := none :: before
      current := some false
      right := (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ state).map some ++ none :: tail },
    outputTape := output }

def prepareCanonicalStateFinish (before tail : List (Option Bool))
    (first second state : List Bool) (output : Tape) : Configuration :=
  { pc := 17,
    inputTape := { ({ right := state.map some ++ none :: tail } : Tape).moveRight with
      left := (FiniteBitEncoding.delimit second).reverse.map some ++
        (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: none :: before },
    outputTape := output, halted := true }

def prepareCanonicalStateSteps (first second : List Bool) : Nat :=
  1 + (4*first.length + 3) + (4*second.length + 3) + 1

theorem prepareCanonicalState_runs (before tail : List (Option Bool))
    (first second state : List Bool) (output : Tape) :
    RunsFor prepareCanonicalState (prepareCanonicalStateStart before tail first second state output)
      (prepareCanonicalStateFinish before tail first second state output) (prepareCanonicalStateSteps first second) := by
  let b₁ := some false :: none :: before
  let b₂ := (FiniteBitEncoding.delimit first).reverse.map some ++ b₁
  let stateCells := state.map some ++ none :: tail
  let firstTail := (FiniteBitEncoding.delimit second).map some ++ stateCells
  let start₁ := skipDelimitedStart b₁ first firstTail output
  have hMove : Step prepareCanonicalState (prepareCanonicalStateStart before tail first second state output)
      (start₁.rebasePc 1) := by
    cases first <;> simp [Step, successors, next, prepareCanonicalState, prepareCanonicalStateStart,
      start₁, skipDelimitedStart_layout, b₁, firstTail, stateCells,
      Instruction.next, Configuration.rebasePc, Configuration.updateTape, Configuration.advance,
      List.map_append, List.append_assoc, Tape.moveRight, FiniteBitEncoding.delimit]
  have hFirst := (skipDelimited_runs b₁ first firstTail output).withSubroutine_halted_of_closed
    [.moveRight .input] skipDelimited (skipDelimited.asSubroutine 9 17 ++ [.halt]) 9
    (by change 0 < 7; decide) rfl rfl skipDelimited_control_closed
  change RunsFor prepareCanonicalState (start₁.rebasePc 1)
    ((skipDelimitedFinish b₁ first firstTail output).resumeAt 9) (4*first.length + 3) at hFirst
  have hSecondStart : (skipDelimitedFinish b₁ first firstTail output).resumeAt 9 =
      (skipDelimitedStart b₂ second stateCells output).rebasePc 9 := by
    simp [skipDelimitedFinish_layout_cells, skipDelimitedStart_layout, b₂, firstTail,
      Configuration.resumeAt, Configuration.rebasePc]
  rw [hSecondStart] at hFirst
  have hSecond := (skipDelimited_runs b₂ second stateCells output).withSubroutine_halted_of_closed
    ([.moveRight .input] ++ skipDelimited.asSubroutine 1 9) skipDelimited [.halt] 17
    (by change 0 < 7; decide) rfl rfl skipDelimited_control_closed
  have hFinish : (skipDelimitedFinish b₂ second stateCells output).resumeAt 17 =
      (prepareCanonicalStateFinish before tail first second state output).resumeAt 17 := by
    simp [skipDelimitedFinish_layout_cells, prepareCanonicalStateFinish, b₂, b₁, stateCells,
      Configuration.resumeAt, List.append_assoc]
  rw [hFinish] at hSecond
  change RunsFor prepareCanonicalState ((skipDelimitedStart b₂ second stateCells output).rebasePc 9)
    ((prepareCanonicalStateFinish before tail first second state output).resumeAt 17) (4*second.length + 3) at hSecond
  have hHalt : Step prepareCanonicalState
      ((prepareCanonicalStateFinish before tail first second state output).resumeAt 17)
      (prepareCanonicalStateFinish before tail first second state output) := by
    simp [Step, successors, next, prepareCanonicalState, skipDelimited,
      Program.asSubroutine, Instruction.asSubroutine, prepareCanonicalStateFinish,
      Configuration.resumeAt, Instruction.next]
  simpa only [prepareCanonicalStateSteps] using
    RunsFor.succ (((RunsFor.succ (RunsFor.zero _) hMove).trans hFirst).trans hSecond) hHalt

theorem prepareCanonicalState_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareCanonicalState := by
  simp [prepareCanonicalState, skipDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareCanonicalState_eval (before tail : List (Option Bool))
    (first second state : List Bool) (output : Tape) :
    evalConfigWithin prepareCanonicalState (prepareCanonicalStateStart before tail first second state output)
      (prepareCanonicalStateSteps first second) =
      PMF.pure (prepareCanonicalStateFinish before tail first second state output) :=
  (prepareCanonicalState_runs _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit prepareCanonicalState_no_randomBit

theorem prepareCanonicalState_steps_eq (first second : List Bool) :
    prepareCanonicalStateSteps first second = 4*(first.length + second.length) + 8 := by
  simp [prepareCanonicalStateSteps]
  omega

set_option maxHeartbeats 400000 in
theorem prepareCanonicalState_control_closed (c d : Configuration)
    (hPc : c.pc < prepareCanonicalState.length) (step : Step prepareCanonicalState c d)
    (_hRunning : d.halted = false) : d.pc < prepareCanonicalState.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 18 at hPc
  change d.pc < 18
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareCanonicalState, skipDelimited,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
