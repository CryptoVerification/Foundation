import Foundation.Constructions.ElGamal.MachineNormalization
import Foundation.Machine.GuessBodyPreparation
import Foundation.Machine.GuessInputPreparation

namespace Machine.Examples

example : prepareCopiedGuess.length = 8 := rfl
example : finishCopiedGuess.length = 38 := rfl

example (saved : List (Option Bool)) (blanks : Nat) :
    RunsFor prepareCopiedGuess (prepareCopiedGuessStart saved [] true [true, true] blanks)
      (prepareCopiedGuessFinish saved [] true [true, true] blanks) 16 :=
  prepareCopiedGuess_runs _ _ _ _ _

example : finishCopiedGuessSteps [] = 17 := rfl
example : finishCopiedGuessSteps [true, true] = 31 := rfl

/-- The old raw source output is gone from the final output tape. Saved
input data remain on the input tape and are not emitted as DDH output. -/
example (saved : List (Option Bool)) (blanks : Nat) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart saved [] true [true, true] blanks) 31).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [true]) :=
  finishCopiedGuess_evalResult _ _ _ _

example (saved : List (Option Bool)) (blanks : Nat) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart saved [] false [] blanks) 17).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [true]) :=
  finishCopiedGuess_evalResult _ _ _ _

example (saved : List (Option Bool)) (blanks : Nat) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart saved [] true [true, true, false] blanks) 36).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [false]) :=
  finishCopiedGuess_evalResult _ _ _ _

example (saved : List (Option Bool)) (blanks : Nat) (c : Configuration)
    (run : PaddedRunsFor finishCopiedGuess
      (prepareCopiedGuessStart saved [] true [true, true] blanks) c 31) : c.halted = true :=
  finishCopiedGuess_haltsFrom _ _ _ _ c run

example (E : FiniteBitEncoding Bool) (source : Program) (input : List Bool)
    (saved : List (Option Bool)) (challenge : Bool) (c : Configuration) :
    (evalConfigWithin finishCopiedGuess
      ((GuardedCompiler.rawResultFrom source input saved [some challenge] c).resumeAt 0)
      (finishCopiedGuessSteps c.outputBits)).map (fun d => (d.halted, d.outputBits)) =
      PMF.pure (true, [ElGamal.interpretGuessResponse E c.outputBits == challenge]) :=
  ElGamal.finishCopiedGuess_correct E source input saved challenge c


-- The complete native body preparation stops even when the retained
-- choose response, DDH tuple or product are malformed. The bound is coarse
-- and linear in physical storage; every configuration is actually retained.
example (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000000 ∧
      RunsFor prepareGuessBody
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareGuessBody_terminates_from_anyTape _ _

-- The same certificate supplies the all-branch premise needed by the
-- probabilistic subroutine composition theorem at a common caller budget.
example (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessBody
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000000)) :
    finish.halted = true := prepareGuessBody_haltsFrom_anyTape _ _ _ trace

-- The same bounded native execution retains a blank current output cell
-- and blank right-hand scratch, even for malformed retained input blocks.
example (input : Tape) (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000000000000000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000000000000000000000 ∧
      RunsFor prepareGuessBody
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } :=
  prepareGuessBody_terminates_with_output_layout _ _ _

-- Public-prefix assembly preserves that frontier for arbitrary retained
-- cells. Its actual input head is restored to the true bit preceding the
-- suffix that the following scratch scans will consume.
example (input : Tape) (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000000 ∧
      RunsFor prepareGuessPrefix
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = some true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } :=
  prepareGuessPrefix_terminates_with_output_layout _ _ _

-- This includes the retained-input rewinds, public-prefix assembly, scratch
-- scans and saved-body framing. All branch bounds quantify over raw inputs;
-- protocol validity is not a premise of this standalone machine property.
example : PolynomialTime prepareGuessInput := prepareGuessInput_polynomialTime

-- Five scans reach blank scratch from any suffix of the retained five
-- bit blocks. The bitstrings themselves may contain malformed frames or
-- arbitrary normalizer replies; their cryptographic validity is irrelevant.
example (before : List (Option Bool)) (output : Tape)
    (first second third fourth fifth : List Bool) (padding count : Nat) (bit : Bool) :
    let input : Tape :=
      { left := before, current := some bit,
        right := (first.map some ++ none :: second.map some ++ none :: third.map some ++
          none :: fourth.map some ++ none :: fifth.map some ++ none ::
            List.replicate padding none).drop count }
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := none :: after, right := List.replicate remaining none } :=
  seekGuessInputScratch_terminates_with_separated_frontier _ output
    first second third fourth fifth padding count bit rfl rfl

-- The native request constructor can be called with arbitrary finite tapes,
-- including nonblank data in what a valid protocol would call scratch.
example (input output : Tape) :
    ∃ finish used,
      used ≤ 1000000000000000000000000000000000000000000000000000000 * (input.cells + output.cells) +
        1000000000000000000000000000000000000000000000000000000 ∧
      RunsFor prepareGuessInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareGuessInput_terminates_from_anyTape _ _

-- The reserved separator produced by the five scans is enough for the
-- saved-message continuation. Arbitrary retained output cells are allowed;
-- both actual tape heads return to blank frontiers for subsequent calls.
example (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000 *
        (({ left := none :: savedInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := { left := none :: savedInput, right := List.replicate inputBlanks none },
           outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } :=
  frameSavedMessage_terminates_with_fresh_tapes _ _ _ _

-- State serialization and middle-field copying do not replace or erase
-- retained input cells. Each head move is an actual counted transition.
example {start finish : Configuration} {used : Nat}
    (run : RunsFor serializeGuessState start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape :=
  serializeGuessState_input_position run

example {start finish : Configuration} {used : Nat}
    (run : RunsFor copyStoredMiddleElement start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape :=
  copyStoredMiddleElement_input_position run

-- An arbitrary forward reading position, even beyond the represented
-- right cells, retains the two real separators before the caller boundary.
-- Restoring three blocks exposes only a suffix plus blank padding.
example (before right : List (Option Bool)) (output : Tape) (moves : Nat) :
    let retained : List (Option Bool) := [none, some false, none, some true]
    let input := (Tape.moveRight^[moves])
      ({ left := retained ++ none :: before, current := some false, right := right } : Tape)
    ∃ finish used count padding,
      used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape.current :: finish.inputTape.right =
        (retained.reverse ++ some false :: right ++ List.replicate padding none).drop count :=
  restoreStoredInput_terminates_after_input_moves _ before (some false) right output moves (by decide)

-- The first retained block here is empty, so the current input cell is
-- blank. The four remaining blocks include another empty block. Actual
-- product copying still supplies both fresh return frontiers.
example (beforeInput beforeOutput : List (Option Bool)) (outputBlanks : Nat) :
    let input : Tape :=
      { left := beforeInput,
        right := [some false, none, some true, none, none, some false, none] }
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (input.cells +
        ({ left := beforeOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } :=
  appendStoredGuessProduct_terminates_with_stream_frontier _ beforeOutput outputBlanks
    [] [false] [true] [] [false] 0 0 rfl

-- Actual saved bit blocks are enough for the whole native body, even when
-- the DDH request and raw normalizer reply are malformed. This combines
-- the state, middle-field and product stages on their actual returned tapes.
example (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000000000000000000000000 * (start.inputTape.cells + output.cells) +
        1000000000000000000000000000 ∧
      RunsFor prepareGuessBody start finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } :=
  prepareGuessBody_terminates_with_retained_frontiers _ _ _ _ _ _ _ _ _

-- Both physical frontiers remain ready after the complete request
-- constructor, even when all retained blocks are arbitrary raw strings.
example (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000000000000000000000000000000000000000000000000000 *
        (start.inputTape.cells + output.cells) + 1000000000000000000000000000000000000000000000000000000 ∧
      RunsFor prepareGuessInput start finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } :=
  prepareGuessInput_terminates_with_retained_frontiers _ _ _ _ _ _ _ _ _

end Machine.Examples
