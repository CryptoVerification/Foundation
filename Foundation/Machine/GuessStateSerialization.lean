import Foundation.Machine.ContextualDelimiter
import Foundation.Machine.GuessStatePreparation

namespace Machine

/-- Reserve one output separator, write the guess-request tag, and serialize
exactly the retained source state. The same fourteen native delimiter-writing
instructions read the actual state cells. The framed product and all saved
caller data remain behind the new separator. -/
def serializeGuessState : Program :=
  [.moveRight .output, .write .output true, .moveRight .output] ++
    writeDelimited.asSubroutine 3 18 ++ [.halt]

def serializeGuessStateStart (beforeInput beforeOutput tail : List (Option Bool))
    (state : List Bool) (blanks : Nat) : Configuration :=
  writeDelimitedContextStart beforeInput beforeOutput tail state blanks

def serializeGuessStateFinish (beforeInput beforeOutput tail : List (Option Bool))
    (state : List Bool) (blanks : Nat) : Configuration :=
  { writeDelimitedContextFinish beforeInput (some true :: none :: beforeOutput) tail state (blanks - 2)
      with pc := 18 }

def serializeGuessStateSteps (state : List Bool) : Nat :=
  3 + writeDelimitedSteps state + 1

theorem serializeGuessState_runs (beforeInput beforeOutput tail : List (Option Bool))
    (state : List Bool) (blanks : Nat) :
    RunsFor serializeGuessState (serializeGuessStateStart beforeInput beforeOutput tail state blanks)
      (serializeGuessStateFinish beforeInput beforeOutput tail state blanks) (serializeGuessStateSteps state) := by
  let start := serializeGuessStateStart beforeInput beforeOutput tail state blanks
  let reserved : Configuration := { start with pc := 1, outputTape := start.outputTape.moveRight }
  let tagged : Configuration := { reserved with pc := 2, outputTape := reserved.outputTape.write (some true) }
  let writer := writeDelimitedContextStart beforeInput (some true :: none :: beforeOutput) tail state (blanks - 2)
  have hReserve : Step serializeGuessState start reserved := by
    simp [Step, successors, next, serializeGuessState, start, reserved, Instruction.next,
      Configuration.updateTape, Configuration.advance, serializeGuessStateStart,
      writeDelimitedContextStart_layout]
  have hTag : Step serializeGuessState reserved tagged := by
    simp [Step, successors, next, serializeGuessState, start, reserved, tagged, Instruction.next,
      Configuration.updateTape, Configuration.advance, serializeGuessStateStart,
      writeDelimitedContextStart_layout]
  have hReady : Step serializeGuessState tagged (writer.rebasePc 3) := by
    cases blanks with
    | zero =>
        simp [Step, successors, next, serializeGuessState, start, reserved, tagged, writer,
          serializeGuessStateStart, writeDelimitedContextStart_layout, Configuration.rebasePc,
          Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
    | succ b =>
        cases b <;> simp [Step, successors, next, serializeGuessState, start, reserved, tagged, writer,
          serializeGuessStateStart, writeDelimitedContextStart_layout, Configuration.rebasePc,
          Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write,
          List.replicate_succ]
  have hWrite := (writeDelimitedContext_runs beforeInput (some true :: none :: beforeOutput) tail state
    (blanks - 2)).withSubroutine_halted_of_closed
      [.moveRight .output, .write .output true, .moveRight .output] writeDelimited [.halt] 18
      (by change 0 < 14; decide) rfl rfl writeDelimited_control_closed
  change RunsFor serializeGuessState (writer.rebasePc 3)
    ((serializeGuessStateFinish beforeInput beforeOutput tail state blanks).resumeAt 18)
    (writeDelimitedSteps state) at hWrite
  have hHalt : Step serializeGuessState
      ((serializeGuessStateFinish beforeInput beforeOutput tail state blanks).resumeAt 18)
      (serializeGuessStateFinish beforeInput beforeOutput tail state blanks) := by
    simp [Step, successors, next, serializeGuessState, serializeGuessStateFinish,
      writeDelimitedContextFinish, writeDelimited, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (((RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hReserve) hTag)
    hReady).trans hWrite)) hHalt

theorem serializeGuessState_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ serializeGuessState := by
  simp [serializeGuessState, writeDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem serializeGuessState_eval (beforeInput beforeOutput tail : List (Option Bool))
    (state : List Bool) (blanks : Nat) :
    evalConfigWithin serializeGuessState (serializeGuessStateStart beforeInput beforeOutput tail state blanks)
      (serializeGuessStateSteps state) =
      PMF.pure (serializeGuessStateFinish beforeInput beforeOutput tail state blanks) :=
  (serializeGuessState_runs _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit serializeGuessState_no_randomBit

theorem serializeGuessState_steps_le (state : List Bool) :
    serializeGuessStateSteps state ≤ 8*state.length + 8 := by
  have h := writeDelimitedSteps_le state
  simp only [serializeGuessStateSteps]
  omega

/-- The output contains a contiguous guess tag and delimited state before a
blank separator. This describes cells written by the native execution; it
is not an additional encoding opcode or a free input reload. -/
theorem serializeGuessStateFinish_output_layout (beforeInput beforeOutput tail : List (Option Bool))
    (state : List Bool) (blanks : Nat) :
    (serializeGuessStateFinish beforeInput beforeOutput tail state blanks).outputTape =
      { left := (true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput,
        right := List.replicate (blanks - (2*state.length + 3)) none } := by
  simp [serializeGuessStateFinish, writeDelimitedContextFinish, List.reverse_cons,
    List.map_append, List.append_assoc]
  omega

/-- State restoration supplies exactly the actual cells consumed by this
serializer, including the selected-message and product copies after the
state's terminating blank. Nothing beyond that blank is read or erased. -/
theorem prepareGuessStateFinish_serialization_layout
    (before padding beforeOutput : List (Option Bool))
    (first second state selected product : List Bool) (blanks : Nat) :
    (prepareGuessStateFinish before padding first second state selected product
      { left := beforeOutput, right := List.replicate blanks none }).resumeAt 0 =
      serializeGuessStateStart
        ((FiniteBitEncoding.delimit second).reverse.map some ++
          (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: none :: before)
        beforeOutput (selected.map some ++ none :: product.map some ++ none :: padding) state blanks := by
  simp [prepareGuessStateFinish, prepareCanonicalStateFinish, serializeGuessStateStart,
    writeDelimitedContextStart_layout, Configuration.resumeAt]

set_option maxHeartbeats 400000 in
theorem serializeGuessState_control_closed (c d : Configuration)
    (hPc : c.pc < serializeGuessState.length) (step : Step serializeGuessState c d)
    (_hRunning : d.halted = false) : d.pc < serializeGuessState.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 19 at hPc
  change d.pc < 19
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, serializeGuessState, writeDelimited,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Restore the retained state after multiplication and serialize it in one
finite native continuation. Its entry uses the actual returned product
layout, rather than a newly loaded state input. -/
def prepareGuessStateBody : Program :=
  prepareGuessState.asSubroutine 0 40 ++ serializeGuessState.asSubroutine 40 60 ++ [.halt]

def prepareGuessStateBodyStart (before padding beforeOutput : List (Option Bool))
    (first second state selected product : List Bool) (blanks : Nat) : Configuration :=
  prepareGuessStateStart before padding first second state selected product
    { left := beforeOutput, right := List.replicate blanks none }

def prepareGuessStateBodyFinish (before padding beforeOutput : List (Option Bool))
    (first second state selected product : List Bool) (blanks : Nat) : Configuration :=
  { serializeGuessStateFinish
      ((FiniteBitEncoding.delimit second).reverse.map some ++
        (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: none :: before)
      beforeOutput (selected.map some ++ none :: product.map some ++ none :: padding) state blanks with pc := 60 }

def prepareGuessStateBodySteps (first second state selected product : List Bool) : Nat :=
  prepareGuessStateSteps first second state selected product + serializeGuessStateSteps state + 1

theorem prepareGuessStateBody_runs (before padding beforeOutput : List (Option Bool))
    (first second state selected product : List Bool) (blanks : Nat) :
    RunsFor prepareGuessStateBody (prepareGuessStateBodyStart before padding beforeOutput first second state selected product blanks)
      (prepareGuessStateBodyFinish before padding beforeOutput first second state selected product blanks)
      (prepareGuessStateBodySteps first second state selected product) := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let beforeState := (FiniteBitEncoding.delimit second).reverse.map some ++
    (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: none :: before
  let tail := selected.map some ++ none :: product.map some ++ none :: padding
  have hRestore := (prepareGuessState_runs before padding first second state selected product output).withSubroutine_halted_of_closed
    [] prepareGuessState (serializeGuessState.asSubroutine 40 60 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl rfl prepareGuessState_control_closed
  change RunsFor prepareGuessStateBody
    (prepareGuessStateBodyStart before padding beforeOutput first second state selected product blanks)
    ((prepareGuessStateFinish before padding first second state selected product output).resumeAt 40)
    (prepareGuessStateSteps first second state selected product) at hRestore
  have hStart : (prepareGuessStateFinish before padding first second state selected product output).resumeAt 40 =
      (serializeGuessStateStart beforeState beforeOutput tail state blanks).rebasePc 40 := by
    have h := prepareGuessStateFinish_serialization_layout before padding beforeOutput first second state selected product blanks
    simpa [Configuration.resumeAt, Configuration.rebasePc, output, beforeState, tail] using
      congrArg (fun c : Configuration => c.rebasePc 40) h
  rw [hStart] at hRestore
  have hSerialize := (serializeGuessState_runs beforeState beforeOutput tail state blanks).withSubroutine_halted_of_closed
    (prepareGuessState.asSubroutine 0 40) serializeGuessState [.halt] 60
    (by change 0 < 19; decide) rfl rfl serializeGuessState_control_closed
  change RunsFor prepareGuessStateBody ((serializeGuessStateStart beforeState beforeOutput tail state blanks).rebasePc 40)
    ((prepareGuessStateBodyFinish before padding beforeOutput first second state selected product blanks).resumeAt 60)
    (serializeGuessStateSteps state) at hSerialize
  have hHalt : Step prepareGuessStateBody
      ((prepareGuessStateBodyFinish before padding beforeOutput first second state selected product blanks).resumeAt 60)
      (prepareGuessStateBodyFinish before padding beforeOutput first second state selected product blanks) := by
    simp [Step, successors, next, prepareGuessStateBody, prepareGuessState, restoreStoredInput,
      rewindBitstring, prepareCanonicalState, skipDelimited, serializeGuessState, writeDelimited,
      Program.asSubroutine, Instruction.asSubroutine, prepareGuessStateBodyFinish, serializeGuessStateFinish,
      writeDelimitedContextFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (hRestore.trans hSerialize) hHalt

theorem prepareGuessStateBody_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessStateBody := by
  simp [prepareGuessStateBody, prepareGuessState, restoreStoredInput, rewindBitstring, prepareCanonicalState,
    skipDelimited, serializeGuessState, writeDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareGuessStateBody_eval (before padding beforeOutput : List (Option Bool))
    (first second state selected product : List Bool) (blanks : Nat) :
    evalConfigWithin prepareGuessStateBody
      (prepareGuessStateBodyStart before padding beforeOutput first second state selected product blanks)
      (prepareGuessStateBodySteps first second state selected product) =
      PMF.pure (prepareGuessStateBodyFinish before padding beforeOutput first second state selected product blanks) :=
  (prepareGuessStateBody_runs _ _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit
    prepareGuessStateBody_no_randomBit

theorem prepareGuessStateBody_steps_le (first second state selected product : List Bool) :
    prepareGuessStateBodySteps first second state selected product ≤
      8*(first.length + second.length) + 10*state.length + 2*(selected.length + product.length) + 39 := by
  have h := serializeGuessState_steps_le state
  rw [prepareGuessStateBodySteps, prepareGuessState_steps_eq]
  omega

set_option maxHeartbeats 1600000 in
theorem prepareGuessStateBody_control_closed (c d : Configuration)
    (hPc : c.pc < prepareGuessStateBody.length) (step : Step prepareGuessStateBody c d)
    (_hRunning : d.halted = false) : d.pc < prepareGuessStateBody.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 61 at hPc
  change d.pc < 61
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareGuessStateBody,
    prepareGuessState, restoreStoredInput, rewindBitstring, prepareCanonicalState, skipDelimited, serializeGuessState, writeDelimited, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
