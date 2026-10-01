import Foundation.Machine.GuessStateSerialization
import Foundation.Machine.StoredMiddleElementCopy
import Foundation.Machine.StoredGuessProduct

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

end Machine
