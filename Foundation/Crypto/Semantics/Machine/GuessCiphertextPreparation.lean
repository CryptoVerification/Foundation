import Foundation.Crypto.Semantics.Machine.GuessStateSerialization
import Foundation.Crypto.Semantics.Machine.StoredMiddleElementCopy
import Foundation.Crypto.Semantics.Machine.StoredGuessProduct

namespace Machine

private def retainedDDHInput (n : Nat) (instanceBits first second last : List Bool) : List Bool :=
  encodeSecurityParameter n ++ frame instanceBits ++
    frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)

/-- Continue from the end of the retained canonical choose response. Restore
the DDH request by native head scans, then append its second delimited field
(the ciphertext's first component) to the already serialized guess state.
The multiplication result is still retained after the selected scratch. -/
def prepareGuessCiphertextFirst : Program :=
  restoreStoredInput.asSubroutine 0 19 ++ copyStoredMiddleElement.asSubroutine 19 74 ++ [.halt]

def prepareGuessCiphertextFirstStart (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Configuration :=
  restoreStoredInputStart before (retainedDDHInput n instanceBits first second last) reply
    (canonicalMessageBits message₀ message₁ state) none
    (selected.map some ++ none :: product.map some ++ none :: padding)
    { left := (true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput }

def prepareGuessCiphertextFirstFinish (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Configuration :=
  { copyStoredMiddleElementFinish before
      ((true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput)
      (reply.map some ++ none :: (canonicalMessageBits message₀ message₁ state).map some ++
        none :: selected.map some ++ none :: product.map some ++ none :: padding)
      n instanceBits first second last with pc := 74 }

def prepareGuessCiphertextFirstSteps
    (n : Nat) (instanceBits first second last reply message₀ message₁ state : List Bool) : Nat :=
  restoreStoredInputSteps (retainedDDHInput n instanceBits first second last) reply
    (canonicalMessageBits message₀ message₁ state) +
    copyStoredMiddleElementSteps n instanceBits first second last + 1

theorem prepareGuessCiphertextFirst_runs (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    RunsFor prepareGuessCiphertextFirst
      (prepareGuessCiphertextFirstStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessCiphertextFirstSteps n instanceBits first second last reply message₀ message₁ state) := by
  let original := retainedDDHInput n instanceBits first second last
  let canonical := canonicalMessageBits message₀ message₁ state
  let stateOutput := (true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput
  let following := selected.map some ++ none :: product.map some ++ none :: padding
  let output : Tape := { left := stateOutput }
  let tail := reply.map some ++ none :: canonical.map some ++ none :: following
  have hRestore := (restoreStoredInput_runs before original reply canonical none following output).withSubroutine_halted_of_closed
    [] restoreStoredInput (copyStoredMiddleElement.asSubroutine 19 74 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor prepareGuessCiphertextFirst
    (prepareGuessCiphertextFirstStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
    ((restoreStoredInputFinish before original reply canonical none following output).resumeAt 19)
    (restoreStoredInputSteps original reply canonical) at hRestore
  have hCopyStart : (restoreStoredInputFinish before original reply canonical none following output).resumeAt 19 =
      (copyStoredMiddleElementStart before stateOutput tail n instanceBits first second last).rebasePc 19 := by
    cases n <;> simp [restoreStoredInputFinish, copyStoredMiddleElementStart_layout, original,
      retainedDDHInput, output, tail, Configuration.resumeAt, Configuration.rebasePc,
      encodeSecurityParameter, List.map_append, List.map_replicate, List.replicate_succ,
      Tape.moveRight, List.append_assoc]
  rw [hCopyStart] at hRestore
  have hCopy := (copyStoredMiddleElement_runs before stateOutput tail n instanceBits first second last).withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) copyStoredMiddleElement [.halt] 74
    (by change 0 < 54; decide) rfl rfl copyStoredMiddleElement_control_closed
  have hCopyFinish : copyStoredMiddleElementFinish before stateOutput tail n instanceBits first second last =
      { prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product with pc := 53 } := by
    simp [prepareGuessCiphertextFirstFinish, copyStoredMiddleElementFinish, stateOutput, tail,
      canonical, following, List.append_assoc]
  rw [hCopyFinish] at hCopy
  change RunsFor prepareGuessCiphertextFirst
    ((copyStoredMiddleElementStart before stateOutput tail n instanceBits first second last).rebasePc 19)
    ((prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 74)
    (copyStoredMiddleElementSteps n instanceBits first second last) at hCopy
  have hHalt : Step prepareGuessCiphertextFirst
      ((prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 74)
      (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product) := by
    simp [Step, successors, next, prepareGuessCiphertextFirst, restoreStoredInput, rewindBitstring,
      copyStoredMiddleElement, skipUnary, skipFrame, skipDelimited, copyDelimited,
      Program.asSubroutine, Instruction.asSubroutine, prepareGuessCiphertextFirstFinish,
      copyStoredMiddleElementFinish, copyDelimitedFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (hRestore.trans hCopy) hHalt

theorem prepareGuessCiphertextFirst_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessCiphertextFirst := by
  simp [prepareGuessCiphertextFirst, restoreStoredInput, rewindBitstring, copyStoredMiddleElement,
    skipUnary, skipFrame, skipDelimited, copyDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareGuessCiphertextFirst_eval (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    evalConfigWithin prepareGuessCiphertextFirst
      (prepareGuessCiphertextFirstStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessCiphertextFirstSteps n instanceBits first second last reply message₀ message₁ state) =
      PMF.pure (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product) :=
  (prepareGuessCiphertextFirst_runs _ _ _ _ _ _ _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit
    prepareGuessCiphertextFirst_no_randomBit

/-- The previous native continuation ends at exactly this next entry. Both
statements describe the same finite tapes, including the saved raw reply,
DDH request, selected message and multiplication result. -/
theorem prepareGuessStateBodyFinish_ciphertext_layout
    (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    (prepareGuessStateBodyFinish
      (reply.reverse.map some ++ none :: (retainedDDHInput n instanceBits first second last).reverse.map some ++ none :: before)
      padding beforeOutput message₀ message₁ state selected product 0).resumeAt 0 =
      prepareGuessCiphertextFirstStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product := by
  simp [prepareGuessStateBodyFinish, serializeGuessStateFinish, writeDelimitedContextFinish,
    prepareGuessCiphertextFirstStart, restoreStoredInputStart, canonicalMessageBits,
    Configuration.resumeAt, List.reverse_cons, List.reverse_append, List.map_append, List.append_assoc]

theorem prepareGuessCiphertextFirstFinish_output (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).outputTape =
      { left := (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second)).reverse.map some ++ none :: beforeOutput,
        right := List.replicate (instanceBits.length + 1 - (2*second.length + 1)) none } := by
  simp [prepareGuessCiphertextFirstFinish, copyStoredMiddleElementFinish_output,
    List.reverse_cons, List.reverse_append, List.map_append, List.append_assoc]

theorem prepareGuessCiphertextFirst_steps_le
    (n : Nat) (instanceBits first second last reply message₀ message₁ state : List Bool) :
    prepareGuessCiphertextFirstSteps n instanceBits first second last reply message₀ message₁ state ≤
      5*n + 14*instanceBits.length + 18*first.length + 24*second.length + 7*last.length +
        2*reply.length + 4*(message₀.length + message₁.length) + 2*state.length + 63 := by
  have h := copyStoredMiddleElement_steps_le n instanceBits first second last
  simp [prepareGuessCiphertextFirstSteps, restoreStoredInputSteps, retainedDDHInput,
    encodeSecurityParameter, frame, canonicalMessageBits, FiniteBitEncoding.delimit_length]
  omega

/-- The first ciphertext component is followed by native scans to the very
same product retained by the arithmetic invocation. The selected-message
scratch is one of the crossed blocks, rather than a fresh multiplication
operand or a silently reloaded product. -/
theorem prepareGuessCiphertextFirstFinish_product_layout
    (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 0 =
      appendStoredGuessProductStart
        ((FiniteBitEncoding.delimit second).reverse.map some ++ (FiniteBitEncoding.delimit first).reverse.map some ++
          (encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length).reverse.map some ++
          (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: before)
        ((true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second)).reverse.map some ++ none :: beforeOutput)
        padding last reply (canonicalMessageBits message₀ message₁ state) selected product
        (instanceBits.length + 1 - (2*second.length + 1)) := by
  change ({
    inputTape := (copyStoredMiddleElementFinish before
      ((true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput)
      (reply.map some ++ none :: (canonicalMessageBits message₀ message₁ state).map some ++
        none :: selected.map some ++ none :: product.map some ++ none :: padding)
      n instanceBits first second last).inputTape,
    outputTape := (prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).outputTape } : Configuration) = _
  rw [copyStoredMiddleElementFinish_input, prepareGuessCiphertextFirstFinish_output]
  simp [appendStoredGuessProductStart, seekBitstringNextStart_layout, List.append_assoc]

/-- After the actual product-copy continuation, the output cells form the
complete raw guess body: tag, delimited state, delimited first ciphertext
component, then the raw product. All earlier output cells and unused blank
padding are retained. Framing this body is a separate native stage. -/
theorem appendStoredGuessProductFinish_guessBody_output
    (beforeInput beforeOutput padding : List (Option Bool))
    (last reply message₀ message₁ state selected second product : List Bool) (blanks : Nat) :
    (appendStoredGuessProductFinish beforeInput
      ((true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second)).reverse.map some ++ none :: beforeOutput)
      padding last reply (canonicalMessageBits message₀ message₁ state) selected product blanks).outputTape =
      { left := (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).reverse.map some ++ none :: beforeOutput,
        right := List.replicate (blanks - product.length) none } := by
  simp [appendStoredGuessProductFinish, copySegmentFinish, List.reverse_cons, List.reverse_append,
    List.map_append, List.append_assoc]

set_option maxHeartbeats 1600000 in
theorem prepareGuessCiphertextFirst_control_closed (c d : Configuration)
    (hPc : c.pc < prepareGuessCiphertextFirst.length) (step : Step prepareGuessCiphertextFirst c d)
    (_hRunning : d.halted = false) : d.pc < prepareGuessCiphertextFirst.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 75 at hPc
  change d.pc < 75
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareGuessCiphertextFirst,
    restoreStoredInput, rewindBitstring, copyStoredMiddleElement, skipUnary, skipFrame, skipDelimited, copyDelimited, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


/-- Restore retained input and append its middle field on arbitrary finite
tapes. A malformed DDH tuple need not provide a valid ciphertext, but every
native restoration, frame scan and escaped-field copy still stops. -/
private theorem prepareGuessCiphertextFirst_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000000 * (input.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessCiphertextFirst
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreStoredInput_terminates_from_anyTape input output
  obtain ⟨copied, copyTime, hCopyTime, copyRun, copyHalt⟩ :=
    copyStoredMiddleElement_terminates_from_anyTape restored.inputTape restored.outputTape
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput (copyStoredMiddleElement.asSubroutine 19 74 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor prepareGuessCiphertextFirst
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 19) restoreTime at hRestore
  have hCopy := copyRun.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) copyStoredMiddleElement [.halt] 74
    (by change 0 < 54; decide) rfl copyHalt copyStoredMiddleElement_control_closed
  change RunsFor prepareGuessCiphertextFirst (restored.resumeAt 19) (copied.resumeAt 74) copyTime at hCopy
  let finish : Configuration := { copied with pc := 74, halted := true }
  have last : Step prepareGuessCiphertextFirst (copied.resumeAt 74) finish := by
    have code : prepareGuessCiphertextFirst[74]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + copyTime + 1, ?_, RunsFor.succ (hRestore.trans hCopy) last, rfl, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    omega
  · intro before blanks hOutput
    obtain ⟨fresh, freshTime, after, remaining, _hFreshTime, freshRun, freshHalt, freshOutput⟩ :=
      copyStoredMiddleElement_terminates_with_output_layout restored.inputTape before blanks
    rw [restoreOutput, hOutput] at copyRun
    have hSame := copyRun.halted_finish_eq_of_no_randomBit freshRun copyHalt freshHalt copyStoredMiddleElement_no_randomBit
    refine ⟨after, remaining, ?_⟩
    change copied.outputTape = _
    rw [hSame]
    exact freshOutput

theorem prepareGuessCiphertextFirst_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000 * (input.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessCiphertextFirst
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := prepareGuessCiphertextFirst_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Restoring the original input leaves the current output alone, and the
native middle-field parser/copy retains its fresh output frontier. The input
may be a malformed tuple rather than an encoded cryptographic instance. -/
theorem prepareGuessCiphertextFirst_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000 ∧
      RunsFor prepareGuessCiphertextFirst
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    prepareGuessCiphertextFirst_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩

/-- A source head reached by right-only state reading still lies over the
retained request blocks. Restoring three blocks and copying the middle field
exposes a suffix of those same cells, with virtual blank padding if needed.
The output frontier is produced by the actual native copy. -/
theorem prepareGuessCiphertextFirst_terminates_after_input_moves
    (retained beforeInput : List (Option Bool)) (current : Option Bool)
    (right beforeOutput : List (Option Bool)) (outputBlanks moves : Nat)
    (hSeparators : 2 ≤ retained.count none) :
    let input := (Tape.moveRight^[moves])
      ({ left := retained ++ none :: beforeInput, current := current, right := right } : Tape)
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    ∃ finish used after remaining count padding,
      used ≤ 1000000000 * (input.cells + output.cells) + 1000000000 ∧
      RunsFor prepareGuessCiphertextFirst
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } ∧
      finish.inputTape.current :: finish.inputTape.right =
        let rest := (retained.reverse ++ current :: right ++ List.replicate padding none).drop count
        if rest = [] then [none] else rest := by
  dsimp only
  let input := (Tape.moveRight^[moves])
    ({ left := retained ++ none :: beforeInput, current := current, right := right } : Tape)
  let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
  obtain ⟨restored, restoreTime, restoreCount, padding, hRestoreTime, restoreRun, restoreHalt,
    restoreOutput, restoreStream⟩ :=
    restoreStoredInput_terminates_after_input_moves retained beforeInput current right
      output moves hSeparators
  obtain ⟨copied, copyTime, after, remaining, hCopyTime, copyRun, copyHalt, copyOutput⟩ :=
    copyStoredMiddleElement_terminates_with_output_layout restored.inputTape beforeOutput outputBlanks
  obtain ⟨copyMoves, _hMoves, copyInput⟩ := copyStoredMiddleElement_input_position copyRun
  have actualCopy : RunsFor copyStoredMiddleElement
      ({ inputTape := restored.inputTape, outputTape := restored.outputTape } : Configuration)
      copied copyTime := by
    rw [restoreOutput]
    exact copyRun
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput (copyStoredMiddleElement.asSubroutine 19 74 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor prepareGuessCiphertextFirst
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 19) restoreTime at hRestore
  have hCopy := actualCopy.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19) copyStoredMiddleElement [.halt] 74
    (by change 0 < 54; decide) rfl copyHalt copyStoredMiddleElement_control_closed
  change RunsFor prepareGuessCiphertextFirst (restored.resumeAt 19) (copied.resumeAt 74) copyTime at hCopy
  let finish : Configuration := { copied with pc := 74, halted := true }
  have last : Step prepareGuessCiphertextFirst (copied.resumeAt 74) finish := by
    have code : prepareGuessCiphertextFirst[74]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + copyTime + 1, after, remaining, restoreCount + copyMoves, padding, ?_,
    RunsFor.succ (hRestore.trans hCopy) last, rfl, copyOutput, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    change restoreTime ≤ 100 * (input.cells + output.cells) + 100 at hRestoreTime
    change copyTime ≤ 1000000 * (restored.inputTape.cells + output.cells) + 1000000 at hCopyTime
    change restoreTime + copyTime + 1 ≤ 1000000000 * (input.cells + output.cells) + 1000000000
    rw [restoreOutput] at hStorage
    omega
  · change copied.inputTape.current :: copied.inputTape.right = _
    rw [copyInput]
    have hRemaining := GuardedCompiler.moveRight_iterate_remaining restored.inputTape copyMoves
    dsimp only at hRemaining
    rw [restoreStream, List.drop_drop] at hRemaining
    exact hRemaining

theorem prepareGuessCiphertextFirst_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessCiphertextFirst
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000 * (input.cells + output.cells) + 1000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := prepareGuessCiphertextFirst_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessCiphertextFirst_no_randomBit hBound finish trace

end Machine
