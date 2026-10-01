import Foundation.Machine.DelimitedSkip
import Foundation.Machine.MessageSelectionPreparation
import Foundation.Machine.GuardedTrace

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

set_option maxHeartbeats 600000 in
/-- Locating the state only advances the actual retained input head. Empty
fields, missing tags and malformed escaped bits cannot erase earlier blocks
or move before their stored separators. The move count is bounded by the
number of native transitions in the supplied trace. -/
theorem prepareCanonicalState_input_position {start finish : Configuration} {used : Nat}
    (run : RunsFor prepareCanonicalState start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape := by
  apply run.input_moveRight_of_step
  intro c d step
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  by_cases hPc : c.pc < 18
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, prepareCanonicalState, skipDelimited,
      Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : prepareCanonicalState[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 18 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl


/-- The state locator also stops on malformed responses. Its two escaped
field scans use finite input-cell bounds and leave the other tape unchanged. -/
theorem prepareCanonicalState_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000 * (input.cells + output.cells) + 1000 ∧
      RunsFor prepareCanonicalState
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  let firstStart : Configuration := { pc := 1, inputTape := input.moveRight, outputTape := output }
  have advance : Step prepareCanonicalState
      ({ inputTape := input, outputTape := output } : Configuration) firstStart := by
    have code : prepareCanonicalState[0]? = some (.moveRight .input) := rfl
    simp [Step, successors, next, code, firstStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have toFirst := RunsFor.succ (RunsFor.zero _) advance
  obtain ⟨first, firstTime, hFirstTime, firstRun, firstHalt, firstOutput⟩ :=
    skipDelimited_terminates_from_anyTape firstStart.inputTape firstStart.outputTape
  have hFirst := firstRun.withSubroutine_halted_of_closed
    [.moveRight .input] skipDelimited (skipDelimited.asSubroutine 9 17 ++ [.halt]) 9
    (by change 0 < 7; decide) rfl firstHalt skipDelimited_control_closed
  change RunsFor prepareCanonicalState firstStart (first.resumeAt 9) firstTime at hFirst
  have toSecond := toFirst.trans hFirst
  obtain ⟨second, secondTime, hSecondTime, secondRun, secondHalt, secondOutput⟩ :=
    skipDelimited_terminates_from_anyTape first.inputTape first.outputTape
  have hSecond := secondRun.withSubroutine_halted_of_closed
    ([.moveRight .input] ++ skipDelimited.asSubroutine 1 9) skipDelimited [.halt] 17
    (by change 0 < 7; decide) rfl secondHalt skipDelimited_control_closed
  change RunsFor prepareCanonicalState (first.resumeAt 9) (second.resumeAt 17) secondTime at hSecond
  let finish : Configuration := { second with pc := 17, halted := true }
  have last : Step prepareCanonicalState (second.resumeAt 17) finish := by
    have code : prepareCanonicalState[17]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, 1 + firstTime + secondTime + 1, ?_,
    RunsFor.succ (toSecond.trans hSecond) last, rfl, secondOutput.trans firstOutput⟩
  have firstStorage := GuardedCompiler.sourceStorage_le_of_run toFirst
  change firstStart.inputTape.cells + firstStart.outputTape.cells ≤ input.cells + output.cells + 1 at firstStorage
  have secondStorage := GuardedCompiler.sourceStorage_le_of_run toSecond
  change first.inputTape.cells + first.outputTape.cells ≤ input.cells + output.cells + (1 + firstTime) at secondStorage
  omega


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem prepareCanonicalState_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareCanonicalState
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000 * (input.cells + output.cells) + 1000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted, _output⟩ :=
    prepareCanonicalState_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareCanonicalState_no_randomBit hBound finish trace

end Machine
