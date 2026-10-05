import Foundation.Crypto.Semantics.Machine.MultiplyOperandPreparation
import Foundation.Crypto.Semantics.Machine.StoredCallPreparation

namespace Machine

/-- Saved cells just before the raw final DDH component. This is a layout
specification for existing encoded input, not a machine instruction. -/
def multiplyCallBeforeElement (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last : List Bool) : List (Option Bool) :=
  (FiniteBitEncoding.delimit second).reverse.map some ++
    (FiniteBitEncoding.delimit first).reverse.map some ++
    (encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length).reverse.map some ++
    (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: before

/-- The completed operand preparation is the actual input to the native
call preparation. All four retained blocks and both sets of represented
blank padding occur in this equality of full configurations. -/
theorem prepareMultiplyOperandsFinish_call_layout (before savedOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).resumeAt 0 =
      prepareStoredCallStart (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: savedOutput) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2 * last.length + 1)) := by
  have hInput := prepareMultiplyOperandsFinish_input before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  have hOutput := prepareMultiplyOperandsFinish_output before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  change ({
    inputTape := (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).inputTape
    outputTape := (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).outputTape } : Configuration) = _
  rw [hInput, hOutput]
  simp [prepareStoredCallStart, seekBitstringNextStart_layout, multiplyCallBeforeElement, List.append_assoc]

/-- Charge the frontier scans and request rewind on the actual returned
arithmetic operand configuration. No request bits are supplied again by a
fresh initial-configuration operation. -/
theorem prepareMultiplyOperandsFinish_call_eval (before savedOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    evalConfigWithin prepareStoredCall
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (prepareStoredCallSteps last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)) =
      PMF.pure (prepareStoredCallFinish (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: savedOutput) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2 * last.length + 1))) := by
  rw [prepareMultiplyOperandsFinish_call_layout]
  exact prepareStoredCall_eval _ _ _ _ _ _ _ _ _

/-- Arbitrary raw replies and malformed stored DDH bits still reach the
actual multiplication-call input frontier. Message framing, operand
restoration/framing, and all four call-preparation scans run successively
on their real returned tapes. The final input current/right cells are all
blank, with one polynomial bound on the total charged preparation time. -/
theorem prepareMultiplyMessage_operands_call_terminate_with_input_frontier
    (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before)
      original reply canonical inputBlanks output
    ∃ messageFinish operandFinish callFinish messageTime operandTime callTime saved remaining,
      messageTime + operandTime + callTime ≤
        10000000000000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
        10000000000000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧ messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      RunsFor prepareStoredCall (operandFinish.resumeAt 0) callFinish callTime ∧
      callFinish.halted = true ∧ callFinish.inputTape.current = none ∧
      ∀ i, callFinish.inputTape.right.getD i none = none := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start := seekStoredInputScratchStart
    (originalPrefix.reverse.map some ++ none :: before)
    original reply canonical inputBlanks output
  obtain ⟨messageFinish, operandFinish, messageTime, operandTime, saved, remaining,
    moves, selected, remainingInput, hTime, messageRun, messageHalt, operandRun,
    operandHalt, _hMoves, hOutput, hCurrent, hRight⟩ :=
    prepareMultiplyMessage_operands_terminate_with_input_output_layout
      before savedOutput originalPrefix original reply canonical inputBlanks outputBlanks
  let restored := restoreInputBeforeScratchFinish before (originalPrefix ++ original)
    reply canonical selected (List.replicate remainingInput none) {}
  let cells := (originalPrefix ++ original).map some ++ none :: reply.map some ++
    none :: canonical.map some ++ none :: selected.map some ++ none :: List.replicate remainingInput none
  have hRaw : restored.inputTape.current :: restored.inputTape.right = cells := by
    cases hOriginal : originalPrefix ++ original <;>
      simp [restored, cells, restoreInputBeforeScratchFinish, restoreStoredInputFinish,
        Tape.moveRight, hOriginal, List.append_assoc]
  have hMoved : ∀ i,
      (((Tape.moveRight^[moves]) restored.inputTape).current ::
        ((Tape.moveRight^[moves]) restored.inputTape).right).getD i none = (cells.drop moves).getD i none := by
    intro i
    rw [GuardedCompiler.moveRight_iterate_remaining, hRaw]
    split
    · rename_i hEmpty
      simp [hEmpty]
    · rfl
  have hCells : ∀ i, (operandFinish.inputTape.current :: operandFinish.inputTape.right).getD i none =
      (cells.drop moves).getD i none := by
    intro i
    have hPhysical : (operandFinish.inputTape.current :: operandFinish.inputTape.right).getD i none =
        (((Tape.moveRight^[moves]) restored.inputTape).current ::
          ((Tape.moveRight^[moves]) restored.inputTape).right).getD i none := by
      cases i with
      | zero => simpa only [List.getD_cons_zero] using hCurrent
      | succ i => simpa only [List.getD_cons_succ] using hRight i
    exact hPhysical.trans (hMoved i)
  obtain ⟨callFinish, callTime, hCallTime, callRun, callHalt⟩ :=
    prepareStoredCall_terminates_from_anyTape operandFinish.inputTape operandFinish.outputTape
  change RunsFor prepareStoredCall (operandFinish.resumeAt 0) callFinish callTime at callRun
  have hFrontier := prepareStoredCall_halted_input_frontier_of_retained_suffix
    operandFinish.inputTape operandFinish.outputTape
    (originalPrefix ++ original) reply canonical selected remainingInput moves hCells callRun callHalt
  refine ⟨messageFinish, operandFinish, callFinish, messageTime, operandTime, callTime,
    saved, remaining, ?_, messageRun, messageHalt, operandRun, operandHalt, hOutput,
    callRun, callHalt, hFrontier⟩
  have hMessageStorage := GuardedCompiler.sourceStorage_le_of_run messageRun
  change GuardedCompiler.sourceStorage messageFinish ≤ GuardedCompiler.sourceStorage start + messageTime at hMessageStorage
  have hOperandStorage := GuardedCompiler.sourceStorage_le_of_run operandRun
  change GuardedCompiler.sourceStorage operandFinish ≤ GuardedCompiler.sourceStorage messageFinish + operandTime at hOperandStorage
  change callTime ≤ 1000000 * GuardedCompiler.sourceStorage operandFinish + 1000000 at hCallTime
  change messageTime + operandTime ≤
    1000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
    1000000000000000000000000000000 at hTime
  change messageTime + operandTime + callTime ≤
    10000000000000000000000000000000000000000 * GuardedCompiler.sourceStorage start +
    10000000000000000000000000000000000000000
  omega

end Machine
