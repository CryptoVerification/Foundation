import Foundation.Machine.CanonicalStatePreparation
import Foundation.Machine.StoredInputRewind
import Foundation.Machine.ReturnedResultInvocation

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

end Machine
