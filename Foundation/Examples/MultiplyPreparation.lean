import Foundation.Constructions.ElGamal.MachineMultiplication
import Foundation.Examples.MachinePolynomialTime
import Foundation.Crypto.Semantics.Machine.GuessStatePreparation
import Foundation.Crypto.Semantics.Machine.SelectedMultiplyCompletion
import Foundation.Crypto.Semantics.Machine.NormalizedGuessCompletion
import Foundation.Crypto.Semantics.Machine.NormalizationGuessCompletion
import Foundation.Examples.GuessCompletion

namespace Foundation.Examples.MultiplyPreparation

open Machine Machine.GuardedCompiler

-- Runtime safety is independent of valid DDH/choose fields. These traces
-- use the actual native scans and framing instructions on retained tapes,
-- including internal blanks or dirty output cells.
example (input output : Tape) :
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor seekStoredInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output :=
  seekStoredInputScratch_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 200 * (input.cells + output.cells) + 200 ∧
      RunsFor writeFrame
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := writeFrame_terminates_from_anyTape _ _

-- The false delimiter is temporarily changed by real instructions and is
-- restored afterwards, together with the exact input head and stored tail.
example (before output tail : List (Option Bool)) (bits : List Bool) (blanks : Nat) :
    (writeFrameAfterFalseFinish before output tail bits blanks).inputTape =
      (writeFrameAfterFalseStart before output tail bits blanks).inputTape := rfl

-- Empty payloads still have a frame. Explicit unused blanks remain in the
-- returned configuration; the routine does not normalize either tape.
example : evalConfigWithin writeFrameAfterFalse
    (writeFrameAfterFalseStart [some true] [some false] [some true, none] [] 12)
    (writeFrameAfterFalseSteps []) =
      PMF.pure (writeFrameAfterFalseFinish [some true] [some false] [some true, none] [] 12) :=
  writeFrameAfterFalse_eval _ _ _ _ _

example : (writeFrameAfterFalseFinish [some true] [some false] [some true, none] [] 12).outputTape =
    { left := [some false, some false], right := List.replicate 11 none } := rfl

-- Saved challenge data remains behind the selected message and the two
-- separators while the message frame is appended to the public prefix.
example (challenge : Bool) (publicBits message : List Bool) :
    (frameSavedMessageFinish [] [some challenge] publicBits message 50).outputTape.left =
      (publicBits ++ frame message).reverse.map some ++
        none :: none :: message.reverse.map some ++ [none, some challenge] := rfl

example (challenge : Bool) (publicBits message : List Bool) :
    evalConfigWithin frameSavedMessage
      (frameSavedMessageStart [] [some challenge] publicBits message 50)
      (frameSavedMessageSteps publicBits message) =
      PMF.pure (frameSavedMessageFinish [] [some challenge] publicBits message 50) :=
  frameSavedMessage_eval _ _ _ _ _

-- Both operands are assembled from retained caller data. The selected
-- message precedes the final DDH component, including when either is empty.
example (before saved padding : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) :
    (prepareMultiplyOperandsFinish before saved padding n instanceBits first second last
      reply canonical selected).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).reverse.map some ++
          none :: none :: selected.reverse.map some ++ none :: saved,
        right := List.replicate (instanceBits.length + 1 - (2*last.length + 1)) none } :=
  prepareMultiplyOperandsFinish_output _ _ _ _ _ _ _ _ _ _ _

-- This invokes the native call preparer on the actual returned operand
-- configuration. No fresh initial configuration supplies the request.
example (before saved : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    evalConfigWithin prepareStoredCall
      ((prepareMultiplyOperandsFinish before saved (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (prepareStoredCallSteps last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)) =
      PMF.pure (prepareStoredCallFinish
        (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: saved) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2*last.length + 1))) :=
  prepareMultiplyOperandsFinish_call_eval _ _ _ _ _ _ _ _ _ _ _

-- A genuinely random source returns its fair bit through the actual
-- guarded call. The observer removes saved caller bits only mathematically;
-- the continuation must still inspect or move those cells natively.
example (challenge : Bool) :
    (evalConfigWithin (storedCallCompile Machine.Examples.randomOutputBit)
      (prepareStoredCallStart [some challenge] [] [] [true] [false] [] [] 4 9)
      (storedCallTraceBudget (fun _ => 2) [] [true] [false] [] [])).map
        (fun c => (c.halted, c.inputTape.bits.drop 3)) =
      Foundation.Probability.sampleBit.map (fun bit => (true, [bit])) := by
  have h := storedCallCompile_evalResult Machine.Examples.randomOutputBit
    [some challenge] [] [] [true] [false] [] [] 4 9 (fun _ => 2)
    (Machine.Examples.randomOutputBit_haltsWithin)
  simpa using h.trans (by
    rw [Machine.Examples.randomOutputBit_eval, PMF.map_comp]
    rfl)

example (q : Nat → Nat) (first second third fourth request : List Bool) :
    storedCallTraceBudget q first second third fourth request ≤
      150*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := storedCallTraceBudget_bound _ _ _ _ _ _

-- A returned empty result is framed as one false bit by the native
-- continuation, after the source halt and with nonempty stored caller data.
example :
    (evalConfigWithin (storedFramedCallCompile Machine.Examples.haltImmediately)
      (prepareStoredCallStart [some true] [some false] [true, false] [] [true] [] [] 7 9)
      (storedFramedCallTraceBudget (fun _ => 1) [true, false] [] [true] [] [])).map
        (fun c => (c.halted, c.outputTape.left.getD 0 none)) =
      PMF.pure (true, some false) := by
  have hCorrect : evalWithin Machine.Examples.haltImmediately [] 1 = PMF.pure (some []) := by
    simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
      Machine.Examples.haltImmediately, Configuration.initial, Configuration.outputBits,
      Tape.bits, PMF.pure_bind, PMF.pure_map]
  have h := storedFramedCallCompile_evalFrameCells Machine.Examples.haltImmediately
    [some true] [some false] [true, false] [] [true] [] [] [] 7 9 (fun _ => 1)
    (Machine.Examples.haltImmediately_haltsWithin []) hCorrect
  have hCell := congrArg
    (fun law : PMF (Bool × (Fin (frame []).length → Option Bool)) =>
      law.map (fun result => (result.1, result.2 ⟨0, by decide⟩))) h
  simpa [PMF.map_comp, PMF.pure_map, Function.comp_def, frame] using hCell

-- Native guess-state restoration reaches the empty state at its actual
-- blank separator. Selected-message scratch and product bits remain after
-- that separator, and the product frame on the other tape is unchanged.
example (output : Tape) :
    evalConfigWithin prepareGuessState
      (prepareGuessStateStart [some true, none, some false] [none, none]
        [true] [false] [] [true] [false, true] output)
      (prepareGuessStateSteps [true] [false] [] [true] [false, true]) =
      PMF.pure (prepareGuessStateFinish [some true, none, some false] [none, none]
        [true] [false] [] [true] [false, true] output) := prepareGuessState_eval _ _ _ _ _ _ _ _

example (output : Tape) :
    (prepareGuessStateFinish [some true] [] [true] [false] [] [true] [false, true] output).inputTape.current = none := rfl

example (before padding : List (Option Bool)) (first second state selected product : List Bool) (output : Tape) :
    (prepareGuessStateFinish before padding first second state selected product output).outputTape = output := rfl

example (q : Nat → Nat) (first second third fourth request : List Bool) :
    storedFramedCallTraceBudget q first second third fourth request ≤
      225*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := storedFramedCallTraceBudget_bound _ _ _ _ _ _


-- Native preparation also stops on malformed retained layouts. The actual
-- intermediate tapes determine the cost; protocol correctness is separate.
example (input output : Tape) :
    ∃ finish used, used ≤ 100000 * (input.cells + output.cells) + 100000 ∧
      RunsFor writeFrameAfterFalse
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := writeFrameAfterFalse_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 200000000 * (input.cells + output.cells) + 200000000 ∧
      RunsFor prepareMultiplyMessage
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareMultiplyMessage_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000 * (input.cells + output.cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareMultiplyOperands_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareStoredCall_terminates_from_anyTape _ _

-- The stronger message trace retains all three arbitrary stored blocks.
-- Its recovered selected block is the same physical block passed to the
-- following input restoration, including when the protocol fields are invalid.
example (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before)
      original reply canonical inputBlanks output
    ∃ finish used, ∃ (selected : List Bool), ∃ remainingInput afterOutput remainingOutput,
      used ≤ 200000000 * sourceStorage start + 200000000 ∧
      RunsFor prepareMultiplyMessage start finish used ∧ finish.halted = true ∧
      finish.resumeAt 0 = restoreInputBeforeScratchStart before (originalPrefix ++ original)
        reply canonical selected (List.replicate remainingInput none)
        { left := afterOutput, right := List.replicate remainingOutput none } :=
  prepareMultiplyMessage_terminates_with_restoration_layout _ _ _ _ _ _ _ _

-- The finite saved input itself can contain arbitrary blanks and bits.
-- Native saved-message copying adds one raw block ahead of its separator,
-- preserves those cells, and returns both heads at blank frontiers.
example (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    ∃ finish used, ∃ (payload : List Bool), ∃ remainingInput afterOutput remainingOutput,
      used ≤ 1000000 *
        (({ left := none :: savedInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := { left := none :: savedInput, right := List.replicate inputBlanks none },
           outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = {
        left := payload.reverse.map some ++ none :: savedInput
        right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } :=
  frameSavedMessage_terminates_with_retained_input _ _ _ _

-- Missing field terminators do not invalidate the output-frontier proof.
-- It concerns the real final-element framing instructions on any input.
example (input : Tape) (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 1000000000000 *
        (input.cells + ({ left := beforeOutput, right := List.replicate blanks none } : Tape).cells) + 1000000000000 ∧
      RunsFor frameStoredFinalElement
        ({ inputTape := input,
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } :=
  frameStoredFinalElement_terminates_with_output_layout _ _ _

-- Operand assembly resumes the actual message return on both retained
-- tapes, with one bound for the two native traces. A fresh input head for
-- the following source call remains a separate proof obligation.
example (before savedOutput : List (Option Bool))
    (original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart before original reply canonical inputBlanks output
    ∃ messageFinish operandFinish messageTime operandTime saved remaining,
      messageTime + operandTime ≤
        1000000000000000000000000000000 * sourceStorage start +
        1000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧
      messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } :=
  prepareMultiplyMessage_operands_terminate_with_output_layout _ _ _ _ _ _ _

-- All four native scans have an exact head-position postcondition, on any
-- finite retained input. It records movement rather than assuming that the
-- fourth separator is already the intended empty source-call scratch.
example (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = advance (advance (advance (advance input))) :=
  prepareStoredCall_terminates_with_input_layout _ _

-- The presumed false delimiter need not actually be present for the
-- framing routine to preserve its blank output frontier.
example (input : Tape) (beforeOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used saved remaining,
      used ≤ 100000 *
        (input.cells + ({ left := beforeOutput, right := List.replicate blanks none } : Tape).cells) + 100000 ∧
      RunsFor writeFrameAfterFalse
        ({ inputTape := input,
           outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } :=
  writeFrameAfterFalse_terminates_with_output_layout _ _ _

-- A missing or incorrect presumed delimiter does not alter the remaining
-- current/right input cells. Only its preceding cell is written as false.
-- The statement also permits unrepresented trailing blank cells.
example (input : Tape) (saved : List (Option Bool)) (blanks : Nat)
    {finish : Configuration} {used : Nat}
    (run : RunsFor writeFrameAfterFalse
      ({ inputTape := input,
         outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
      finish used) (hHalted : finish.halted = true) :
    finish.inputTape.current = input.current ∧
      ∀ i, finish.inputTape.right.getD i none = input.right.getD i none :=
  writeFrameAfterFalse_halted_input_cells _ _ _ run hHalted

-- Actual operand preparation consumes raw retained blocks with no valid
-- DDH parsing premise. Its remaining input is a rightward suffix of the
-- restored four-block layout, and its output is still fresh for the caller.
example (before savedOutput : List (Option Bool))
    (original reply canonical selected : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := restoreInputBeforeScratchStart before original reply canonical selected
      (List.replicate inputBlanks none) output
    let restored := restoreInputBeforeScratchFinish before original reply canonical selected
      (List.replicate inputBlanks none) output
    ∃ finish used saved remaining moves,
      used ≤ 1000000000000000000 * sourceStorage start + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands start finish used ∧ finish.halted = true ∧ moves ≤ used ∧
      finish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      finish.inputTape.current = ((Tape.moveRight^[moves]) restored.inputTape).current ∧
      ∀ i, finish.inputTape.right.getD i none =
        ((Tape.moveRight^[moves]) restored.inputTape).right.getD i none :=
  prepareMultiplyOperands_terminates_from_retained_blocks _ _ _ _ _ _ _ _

-- The source input, reply and canonical response may all be malformed.
-- Both traces use the same actual returned tapes; the final input-layout
-- claim now accompanies the common polynomial storage bound.
example (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before)
      original reply canonical inputBlanks output
    ∃ messageFinish operandFinish messageTime operandTime saved remaining moves,
      ∃ (selected : List Bool) (remainingInput : Nat),
      let restored := restoreInputBeforeScratchFinish before (originalPrefix ++ original)
        reply canonical selected (List.replicate remainingInput none) {}
      messageTime + operandTime ≤
        1000000000000000000000000000000 * sourceStorage start +
        1000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧
      messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧ moves ≤ operandTime ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      operandFinish.inputTape.current = ((Tape.moveRight^[moves]) restored.inputTape).current ∧
      ∀ i, operandFinish.inputTape.right.getD i none =
        ((Tape.moveRight^[moves]) restored.inputTape).right.getD i none :=
  prepareMultiplyMessage_operands_terminate_with_input_output_layout _ _ _ _ _ _ _ _

-- A concrete malformed original and raw canonical reply still traverse
-- the three actual native stages. There is no valid DDH serialization,
-- decoder success, normalizer correctness, or initial blank padding here.
-- The final input head and every right-hand cell are nevertheless blank.
example :
    let start := seekStoredInputScratchStart [none, some false]
      [true] [false, false] [true, false, true] 0 { left := [none, some true] }
    ∃ messageFinish operandFinish callFinish messageTime operandTime callTime saved remaining,
      messageTime + operandTime + callTime ≤
        10000000000000000000000000000000000000000 * sourceStorage start +
        10000000000000000000000000000000000000000 ∧
      RunsFor prepareMultiplyMessage start messageFinish messageTime ∧ messageFinish.halted = true ∧
      RunsFor prepareMultiplyOperands (messageFinish.resumeAt 0) operandFinish operandTime ∧
      operandFinish.halted = true ∧
      operandFinish.outputTape = { left := saved, right := List.replicate remaining none } ∧
      RunsFor prepareStoredCall (operandFinish.resumeAt 0) callFinish callTime ∧
      callFinish.halted = true ∧ callFinish.inputTape.current = none ∧
      ∀ i, callFinish.inputTape.right.getD i none = none :=
  prepareMultiplyMessage_operands_call_terminate_with_input_frontier
    [some false] [none, some true] [] [true] [false, false] [true, false, true] 0 0

-- The same malformed retained input now runs through the actual message
-- constructor, operand constructor, randomized multiplication call,
-- randomized guess call, and final native output cleanup. Stopping uses
-- neither a protocol decoder nor a multiplication-correctness assumption.
example :
    let start := seekStoredInputScratchStart [none, some false]
      [true] [false, false] [true, false, true] 0 { left := [none, some true] }
    ∀ finish, PaddedRunsFor
      (messageMultiplyGuessCompile Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess) start finish
      (messageMultiplyGuessRetainedBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true :=
  messageMultiplyGuessCompile_haltsFrom_retained_frontiers _ _ 4 0 4 0
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    [some false] [none, some true] [] [true] [false, false] [true, false, true] 0 0

example : PolynomiallyBounded (messageMultiplyGuessRetainedBudget 4 0 4 0) :=
  messageMultiplyGuessRetainedBudget_polynomial _ _ _ _


-- Prefix restoration is now part of the stopping theorem. This arbitrary
-- three-bit response is not a canonical pair of delimited messages. The
-- retained caller blocks and output have no extra outer blank padding;
-- both subsequent calls contain native random-bit instructions.
example :
    let start : Configuration := {
      inputTape := {
        left := [some false, some true, none, some true, none, some false]
        current := some false
        right := [some true, some true, none] },
      outputTape := { left := [some true, some false, none] } }
    ∀ finish, PaddedRunsFor
      (selectedMultiplyGuessCompile Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess) start finish
      (selectedMultiplyGuessRetainedBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true :=
  selectedMultiplyGuessCompile_haltsFrom_raw_frontier _ _ 4 0 4 0
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    {
      left := [some false, some true, none, some true, none, some false]
      current := some false
      right := [some true, some true, none] }
    [some true, some false, none] 0 [false, true, true] 0 rfl

-- An empty raw response and entirely unrepresented trailing blank space
-- are covered by the same whole prefix/multiply/guess stopping statement.
example :
    let start : Configuration := {}
    ∀ finish, PaddedRunsFor
      (selectedMultiplyGuessCompile Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess) start finish
      (selectedMultiplyGuessRetainedBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true :=
  selectedMultiplyGuessCompile_haltsFrom_raw_frontier _ _ 4 0 4 0
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    {} [] 0 [] 0 rfl

example : PolynomiallyBounded (selectedMultiplyGuessRetainedBudget 4 0 4 0) :=
  selectedMultiplyGuessRetainedBudget_polynomial _ _ _ _


-- Every possible raw normalizer return, not only a canonical response,
-- enters the actual fair-bit selector and then both randomized native
-- calls. The concrete caller prefixes contain no decoded DDH assumptions.
example (result : Configuration) :
    let returned := (rawResultFrom [.halt] [] [some false] [none, some true] result).swapTapes
    ∀ finish, PaddedRunsFor
      (normalizedMultiplyGuessCompile Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess) (returned.resumeAt 0) finish
      (normalizedMultiplyGuessRetainedBudget 4 0 4 0 (sourceStorage returned)) → finish.halted = true :=
  normalizedMultiplyGuessCompile_fromNormalizer_haltsFrom_raw [.halt] _ _ 4 0 4 0
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    [] [some false] [some true] result

example : PolynomiallyBounded (normalizedMultiplyGuessRetainedBudget 4 0 4 0) :=
  normalizedMultiplyGuessRetainedBudget_polynomial _ _ _ _

-- The normalizer itself is now executed, followed by the entire native
-- challenge/multiply/guess continuation. The one-bit tagged randomized
-- response is not a canonical pair of messages. Every supported random
-- branch is covered, with arbitrary retained caller bits and no padding.
example :
    let start : Configuration := {
      inputTape := {
        left := [some true, some false, none, some true, none, some false] },
      outputTape := { left := [some true, none, some false] } }
    ∀ finish, PaddedRunsFor
      (normalizationChallengeGuessCompile
        Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess
        Foundation.Examples.GuessCompletion.randomTaggedGuess) start finish
      (normalizationChallengeRetainedBudget 4 0 4 0 4 0 (sourceStorage start)) →
      finish.halted = true :=
  normalizationChallengeGuessCompile_haltsFrom_retainedReply _ _ _ 4 0 4 0 4 0
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using Foundation.Examples.GuessCompletion.randomTaggedGuess_haltsWithin request)
    [some true, none, some false] [some true, none, some false] [false, true] 0 0

example : PolynomiallyBounded (normalizationChallengeRetainedBudget 4 0 4 0 4 0) :=
  normalizationChallengeRetainedBudget_polynomial _ _ _ _ _ _

end Foundation.Examples.MultiplyPreparation
