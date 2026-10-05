import Foundation.Crypto.Semantics.Machine.CanonicalStatePreparation
import Foundation.Crypto.Semantics.Machine.StoredInputRewind
import Foundation.Crypto.Semantics.Machine.ReturnedResultInvocation

namespace Machine

/-- From the returned multiplication output, rewind the product, selected
message scratch, and canonical choose response. Locate the state inside that
response by native delimiter scans. The other tape retains the framed product
and all arithmetic scratch; no response or state is loaded again. -/
def prepareGuessState : Program :=
  restoreStoredInput.asSubroutine 0 19 ++ prepareCanonicalState.asSubroutine 19 38 ++ [.halt]

def prepareGuessStateStart (before padding : List (Option Bool))
    (first second state selected product : List Bool) (output : Tape) : Configuration :=
  restoreStoredInputStart before (canonicalMessageBits first second state) selected product none padding output

def prepareGuessStateFinish (before padding : List (Option Bool))
    (first second state selected product : List Bool) (output : Tape) : Configuration :=
  { prepareCanonicalStateFinish before
      (selected.map some ++ none :: product.map some ++ none :: padding) first second state output with pc := 38 }

def prepareGuessStateSteps (first second state selected product : List Bool) : Nat :=
  restoreStoredInputSteps (canonicalMessageBits first second state) selected product +
    prepareCanonicalStateSteps first second + 1

theorem prepareGuessState_runs (before padding : List (Option Bool))
    (first second state selected product : List Bool) (output : Tape) :
    RunsFor prepareGuessState (prepareGuessStateStart before padding first second state selected product output)
      (prepareGuessStateFinish before padding first second state selected product output)
      (prepareGuessStateSteps first second state selected product) := by
  let canonical := canonicalMessageBits first second state
  let tail := selected.map some ++ none :: product.map some ++ none :: padding
  have hRestore := (restoreStoredInput_runs before canonical selected product none padding output).withSubroutine_halted_of_closed
    [] restoreStoredInput (prepareCanonicalState.asSubroutine 19 38 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor prepareGuessState (prepareGuessStateStart before padding first second state selected product output)
    ((restoreStoredInputFinish before canonical selected product none padding output).resumeAt 19)
    (restoreStoredInputSteps canonical selected product) at hRestore
  have hStart : (restoreStoredInputFinish before canonical selected product none padding output).resumeAt 19 =
      (prepareCanonicalStateStart before tail first second state output).rebasePc 19 := by
    simp [restoreStoredInputFinish, prepareCanonicalStateStart, canonical, canonicalMessageBits, tail,
      Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight, List.map_append, List.append_assoc]
  rw [hStart] at hRestore
  have hState := (prepareCanonicalState_runs before tail first second state output).withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) prepareCanonicalState [.halt] 38
    (by change 0 < 18; decide) rfl rfl prepareCanonicalState_control_closed
  change RunsFor prepareGuessState ((prepareCanonicalStateStart before tail first second state output).rebasePc 19)
    ((prepareGuessStateFinish before padding first second state selected product output).resumeAt 38)
    (prepareCanonicalStateSteps first second) at hState
  have hHalt : Step prepareGuessState
      ((prepareGuessStateFinish before padding first second state selected product output).resumeAt 38)
      (prepareGuessStateFinish before padding first second state selected product output) := by
    simp [Step, successors, next, prepareGuessState, restoreStoredInput, rewindBitstring,
      prepareCanonicalState, skipDelimited, Program.asSubroutine, Instruction.asSubroutine,
      prepareGuessStateFinish, prepareCanonicalStateFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (hRestore.trans hState) hHalt

theorem prepareGuessState_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessState := by
  simp [prepareGuessState, restoreStoredInput, rewindBitstring, prepareCanonicalState, skipDelimited,
    Program.asSubroutine, Instruction.asSubroutine]

theorem prepareGuessState_eval (before padding : List (Option Bool))
    (first second state selected product : List Bool) (output : Tape) :
    evalConfigWithin prepareGuessState (prepareGuessStateStart before padding first second state selected product output)
      (prepareGuessStateSteps first second state selected product) =
      PMF.pure (prepareGuessStateFinish before padding first second state selected product output) :=
  (prepareGuessState_runs _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit prepareGuessState_no_randomBit

theorem prepareGuessState_steps_eq (first second state selected product : List Bool) :
    prepareGuessStateSteps first second state selected product =
      8*(first.length + second.length) + 2*(state.length + selected.length + product.length) + 30 := by
  simp [prepareGuessStateSteps, restoreStoredInputSteps, prepareCanonicalStateSteps,
    canonicalMessageBits, FiniteBitEncoding.delimit_length]
  omega

/-- The input tape after the real guarded multiplication call and result
framing has this exact three-block layout. The output includes the product
frame and remains unchanged by state restoration. The canonical response
was already written by the normalizer; it is not supplied by this routine. -/
theorem returnedFrameResult_guessState_layout (source : Program) (request : List Bool)
    (beforeInput beforeCanonical : List (Option Bool)) (first second state selected : List Bool)
    (c : Configuration) :
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits first second state).reverse.map some ++
      none :: beforeCanonical
    let returned := GuardedCompiler.returnedFrameResult source request beforeInput saved c
    returned.resumeAt 0 =
      prepareGuessStateStart beforeCanonical
        (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none)
        first second state selected c.outputBits returned.outputTape := by
  dsimp only
  simp [GuardedCompiler.returnedFrameResult, frameReturnedResultFinish, prepareGuessStateStart,
    restoreStoredInputStart, Configuration.resumeAt, List.append_assoc]

set_option maxHeartbeats 800000 in
theorem prepareGuessState_control_closed (c d : Configuration)
    (hPc : c.pc < prepareGuessState.length) (step : Step prepareGuessState c d)
    (_hRunning : d.halted = false) : d.pc < prepareGuessState.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 39 at hPc
  change d.pc < 39
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareGuessState, restoreStoredInput,
    rewindBitstring, prepareCanonicalState, skipDelimited, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


/-- Restoring three retained blocks and locating the state are safe for
stopping on any finite caller tapes. Malformed choose data can change the
located cells, but cannot invalidate the actual linear-time scan bound. -/
theorem prepareGuessState_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareGuessState
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreStoredInput_terminates_from_anyTape input output
  obtain ⟨located, locateTime, hLocateTime, locateRun, locateHalt, locateOutput⟩ :=
    prepareCanonicalState_terminates_from_anyTape restored.inputTape restored.outputTape
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput (prepareCanonicalState.asSubroutine 19 38 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor prepareGuessState
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 19) restoreTime at hRestore
  have hLocate := locateRun.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) prepareCanonicalState [.halt] 38
    (by change 0 < 18; decide) rfl locateHalt prepareCanonicalState_control_closed
  change RunsFor prepareGuessState (restored.resumeAt 19) (located.resumeAt 38) locateTime at hLocate
  let finish : Configuration := { located with pc := 38, halted := true }
  have last : Step prepareGuessState (located.resumeAt 38) finish := by
    have code : prepareGuessState[38]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + locateTime + 1, ?_, RunsFor.succ (hRestore.trans hLocate) last,
    rfl, locateOutput.trans restoreOutput⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
  change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
  omega


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem prepareGuessState_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessState
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000 * (input.cells + output.cells) + 1000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted, _output⟩ :=
    prepareGuessState_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessState_no_randomBit hBound finish trace

/-- The three stored blocks may be arbitrary raw bitstrings. After their
actual restoration, locating the state only advances from that restored
head position. This retains the earlier request/reply separators even if
the normalizer's response is malformed. -/
theorem prepareGuessState_terminates_with_retained_input
    (before : List (Option Bool)) (first second consumed : List Bool)
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    let start := restoreStoredInputStart before first second consumed current right output
    let restored := restoreStoredInputFinish before first second consumed current right output
    ∃ finish used moves,
      used ≤ 1000000 * (start.inputTape.cells + output.cells) + 1000000 ∧
      RunsFor prepareGuessState start finish used ∧ finish.halted = true ∧
      finish.outputTape = output ∧ moves ≤ used ∧
      finish.inputTape = (Tape.moveRight^[moves]) restored.inputTape := by
  dsimp only
  let start := restoreStoredInputStart before first second consumed current right output
  let restored := restoreStoredInputFinish before first second consumed current right output
  have restoreRun := restoreStoredInput_runs before first second consumed current right output
  change RunsFor restoreStoredInput start restored (restoreStoredInputSteps first second consumed) at restoreRun
  obtain ⟨located, locateTime, hLocateTime, locateRun, locateHalt, locateOutput⟩ :=
    prepareCanonicalState_terminates_from_anyTape restored.inputTape output
  obtain ⟨moves, hMoves, locateInput⟩ := prepareCanonicalState_input_position locateRun
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput (prepareCanonicalState.asSubroutine 19 38 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor prepareGuessState start (restored.resumeAt 19)
    (restoreStoredInputSteps first second consumed) at hRestore
  have hLocate := locateRun.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) prepareCanonicalState [.halt] 38
    (by change 0 < 18; decide) rfl locateHalt prepareCanonicalState_control_closed
  change RunsFor prepareGuessState (restored.resumeAt 19) (located.resumeAt 38) locateTime at hLocate
  let finish : Configuration := { located with pc := 38, halted := true }
  have last : Step prepareGuessState (located.resumeAt 38) finish := by
    have code : prepareGuessState[38]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreStoredInputSteps first second consumed + locateTime + 1, moves,
    ?_, RunsFor.succ (hRestore.trans hLocate) last, rfl, locateOutput, by omega, locateInput⟩
  have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
  change restored.inputTape.cells + output.cells ≤
    start.inputTape.cells + output.cells + restoreStoredInputSteps first second consumed at hStorage
  have hRestoreTime : restoreStoredInputSteps first second consumed ≤
      100 * (start.inputTape.cells + output.cells) + 100 := by
    dsimp only [restoreStoredInputSteps, start, restoreStoredInputStart, Tape.cells]
    simp only [List.length_append, List.length_cons, List.length_map, List.length_reverse]
    omega
  change locateTime ≤ 1000 * (restored.inputTape.cells + output.cells) + 1000 at hLocateTime
  change restoreStoredInputSteps first second consumed + locateTime + 1 ≤
    1000000 * (start.inputTape.cells + output.cells) + 1000000
  omega

end Machine
