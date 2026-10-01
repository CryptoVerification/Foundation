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

set_option maxHeartbeats 600000 in
/-- Serializing even malformed state cells preserves the retained input
contents and only moves the input head to the right. The number of moves
is bounded by the actual native transition count. -/
theorem serializeGuessState_input_position {start finish : Configuration} {used : Nat}
    (run : RunsFor serializeGuessState start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape := by
  apply run.input_moveRight_of_step
  intro c d step
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  by_cases hPc : c.pc < 19
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, serializeGuessState, writeDelimited,
      Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : serializeGuessState[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 19 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

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


/-- State serialization reads only the finite input segment through its
first blank. The separator and request tag are actual writes, even when
caller output storage is already dirty. -/
private theorem serializeGuessState_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 8 * input.cells + 8 ∧
      RunsFor serializeGuessState
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  let reserved : Configuration := { pc := 1, inputTape := input, outputTape := output.moveRight }
  let tagged : Configuration := { reserved with pc := 2, outputTape := reserved.outputTape.write (some true) }
  let writer : Configuration := { tagged with pc := 3, outputTape := tagged.outputTape.moveRight }
  have a : Step serializeGuessState ({ inputTape := input, outputTape := output } : Configuration) reserved := by
    have code : serializeGuessState[0]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, reserved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have b : Step serializeGuessState reserved tagged := by
    have code : serializeGuessState[1]? = some (.write .output true) := rfl
    simp [Step, successors, next, code, reserved, tagged, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step serializeGuessState tagged writer := by
    have code : serializeGuessState[2]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, reserved, tagged, writer, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have toWriter := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c
  obtain ⟨written, writeTime, hWriteTime, writeRun, writeHalt⟩ :=
    writeDelimited_terminates_from_anyTape writer.inputTape writer.outputTape
  have hWrite := writeRun.withSubroutine_halted_of_closed
    [.moveRight .output, .write .output true, .moveRight .output] writeDelimited [.halt] 18
    (by change 0 < 14; decide) rfl writeHalt writeDelimited_control_closed
  change RunsFor serializeGuessState writer (written.resumeAt 18) writeTime at hWrite
  let finish : Configuration := { written with pc := 18, halted := true }
  have last : Step serializeGuessState (written.resumeAt 18) finish := by
    have code : serializeGuessState[18]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, 3 + writeTime + 1, ?_, RunsFor.succ (toWriter.trans hWrite) last, rfl, ?_⟩
  · change writeTime ≤ 8 * input.cells + 4 at hWriteTime
    omega
  · intro before blanks hOutput
    have hEntry : writer.outputTape =
        ({ left := some true :: none :: before, right := List.replicate (blanks - 1 - 1) none } : Tape) := by
      cases blanks with
      | zero => simp [writer, tagged, reserved, hOutput, Tape.moveRight, Tape.write]
      | succ count =>
          cases count <;> simp [writer, tagged, reserved, hOutput, Tape.moveRight, Tape.write, List.replicate_succ]
    obtain ⟨fresh, freshTime, after, remaining, _hFreshTime, freshRun, freshHalt, freshOutput⟩ :=
      writeDelimited_terminates_with_output_layout input (some true :: none :: before) (blanks - 1 - 1)
    rw [hEntry] at writeRun
    have hSame := writeRun.halted_finish_eq_of_no_randomBit freshRun writeHalt freshHalt writeDelimited_no_randomBit
    refine ⟨after, remaining, ?_⟩
    change written.outputTape = _
    rw [hSame]
    exact freshOutput

theorem serializeGuessState_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 8 * input.cells + 8 ∧
      RunsFor serializeGuessState
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := serializeGuessState_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Native state serialization retains a fresh output frontier even when
the retained response is malformed. The same halted execution supplies both
the charged stopping bound and the returned-tape layout. -/
theorem serializeGuessState_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining, used ≤ 8 * input.cells + 8 ∧
      RunsFor serializeGuessState
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    serializeGuessState_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩

/-- The entire retained-state restoration and serialization stage stops on
arbitrary finite tapes. Each stage receives the previous stage's actual
returned tapes, so its bound charges the storage created by earlier steps. -/
private theorem prepareGuessStateBody_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000000 * (input.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessStateBody
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨located, locateTime, hLocateTime, locateRun, locateHalt, locateOutput⟩ :=
    prepareGuessState_terminates_from_anyTape input output
  obtain ⟨serialized, serializeTime, hSerializeTime, serializeRun, serializeHalt, serializeLayout⟩ :=
    serializeGuessState_terminates_core located.inputTape located.outputTape
  have hLocate := locateRun.withSubroutine_halted_of_closed
    [] prepareGuessState (serializeGuessState.asSubroutine 40 60 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl locateHalt prepareGuessState_control_closed
  change RunsFor prepareGuessStateBody
    ({ inputTape := input, outputTape := output } : Configuration) (located.resumeAt 40) locateTime at hLocate
  have hSerialize := serializeRun.withSubroutine_halted_of_closed
    (prepareGuessState.asSubroutine 0 40) serializeGuessState [.halt] 60
    (by change 0 < 19; decide) rfl serializeHalt serializeGuessState_control_closed
  change RunsFor prepareGuessStateBody (located.resumeAt 40) (serialized.resumeAt 60) serializeTime at hSerialize
  let finish : Configuration := { serialized with pc := 60, halted := true }
  have last : Step prepareGuessStateBody (serialized.resumeAt 60) finish := by
    have code : prepareGuessStateBody[60]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, locateTime + serializeTime + 1, ?_, RunsFor.succ (hLocate.trans hSerialize) last, rfl, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run locateRun
    change located.inputTape.cells + located.outputTape.cells ≤ input.cells + output.cells + locateTime at hStorage
    omega
  · intro before blanks hOutput
    exact serializeLayout before blanks (locateOutput.trans hOutput)

theorem prepareGuessStateBody_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000 * (input.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessStateBody
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := prepareGuessStateBody_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Restoring the retained state does not change the other tape, and the
subsequent native serializer retains its fresh output frontier. This does
not require a valid canonical choose response. -/
theorem prepareGuessStateBody_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000 ∧
      RunsFor prepareGuessStateBody
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    prepareGuessStateBody_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem serializeGuessState_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor serializeGuessState
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (8 * input.cells + 8)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    serializeGuessState_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted serializeGuessState_no_randomBit hBound finish trace


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem prepareGuessStateBody_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessStateBody
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000 * (input.cells + output.cells) + 1000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    prepareGuessStateBody_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessStateBody_no_randomBit hBound finish trace

/-- The whole native state restoration and serialization retains its
input origin and a fresh output frontier. Arbitrary raw response blocks
are allowed; the input head only advances after the exact three-block
restoration, so earlier request/reply separators remain available. -/
theorem prepareGuessStateBody_terminates_with_retained_input
    (before : List (Option Bool)) (first second consumed : List Bool)
    (current : Option Bool) (right beforeOutput : List (Option Bool)) (blanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
    let start := restoreStoredInputStart before first second consumed current right output
    let restored := restoreStoredInputFinish before first second consumed current right output
    ∃ finish used moves after remaining,
      used ≤ 1000000000 * (start.inputTape.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessStateBody start finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } ∧
      moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) restored.inputTape := by
  dsimp only
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let start := restoreStoredInputStart before first second consumed current right output
  let restored := restoreStoredInputFinish before first second consumed current right output
  obtain ⟨located, locateTime, locateMoves, hLocateTime, locateRun, locateHalt,
    locateOutput, hLocateMoves, locateInput⟩ :=
    prepareGuessState_terminates_with_retained_input before first second consumed current right output
  obtain ⟨serialized, serializeTime, after, remaining, hSerializeTime,
    serializeRun, serializeHalt, serializeOutput⟩ :=
    serializeGuessState_terminates_with_output_layout located.inputTape beforeOutput blanks
  obtain ⟨serializeMoves, hSerializeMoves, serializeInput⟩ :=
    serializeGuessState_input_position serializeRun
  have actualSerialize : RunsFor serializeGuessState
      ({ inputTape := located.inputTape, outputTape := located.outputTape } : Configuration)
      serialized serializeTime := by
    rw [locateOutput]
    exact serializeRun
  have hLocate := locateRun.withSubroutine_halted_of_closed
    [] prepareGuessState (serializeGuessState.asSubroutine 40 60 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl locateHalt prepareGuessState_control_closed
  change RunsFor prepareGuessStateBody start (located.resumeAt 40) locateTime at hLocate
  have hSerialize := actualSerialize.withSubroutine_halted_of_closed
    (prepareGuessState.asSubroutine 0 40) serializeGuessState [.halt] 60
    (by change 0 < 19; decide) rfl serializeHalt serializeGuessState_control_closed
  change RunsFor prepareGuessStateBody (located.resumeAt 40) (serialized.resumeAt 60) serializeTime at hSerialize
  let finish : Configuration := { serialized with pc := 60, halted := true }
  have last : Step prepareGuessStateBody (serialized.resumeAt 60) finish := by
    have code : prepareGuessStateBody[60]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, locateTime + serializeTime + 1, serializeMoves + locateMoves, after, remaining,
    ?_, RunsFor.succ (hLocate.trans hSerialize) last, rfl, serializeOutput, by omega, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run locateRun
    change located.inputTape.cells + located.outputTape.cells ≤
      start.inputTape.cells + output.cells + locateTime at hStorage
    rw [locateOutput] at hStorage
    change locateTime ≤ 1000000 * (start.inputTape.cells + output.cells) + 1000000 at hLocateTime
    change locateTime + serializeTime + 1 ≤ 1000000000 * (start.inputTape.cells + output.cells) + 1000000000
    omega
  · change serialized.inputTape = (Tape.moveRight^[serializeMoves + locateMoves]) restored.inputTape
    rw [serializeInput, locateInput, Function.iterate_add_apply]

end Machine
