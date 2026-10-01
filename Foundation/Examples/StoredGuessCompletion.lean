import Foundation.Machine.StoredGuessLayout

namespace Foundation.Examples.StoredGuessCompletion

open Machine Machine.GuardedCompiler

/-- The main continuation has eight blocks before the challenge and four
normalizer/choose scratch blocks behind it. Its syntax contains 157 native
instructions, independent of all block contents and the security parameter. -/
example : (finishStoredGuess 8 4).length = 157 := finishStoredGuess_protocol_length

example (input : Tape) (before : List (Option Bool)) (blocks : List (List Bool))
    (right : List (Option Bool)) :
    evalConfigWithin (eraseOutputBlocks blocks.length)
      (eraseOutputBlocksStart input before blocks right) (eraseOutputBlocksSteps blocks) =
      PMF.pure (eraseOutputBlocksFinish input before blocks right) :=
  eraseOutputBlocks_eval input before blocks right

/-- Empty blocks are genuine boundaries and their traversal is charged. -/
example : eraseOutputBlocksSteps [[], [false, true], []] = 21 := rfl

example (input : Tape) (blocks : List (List Bool)) (blanks : Nat) (bit : Bool) :
    (evalConfigWithin (cleanStoredOutputBit blocks.length)
      (cleanStoredOutputBitStart input blocks (List.replicate blanks none) bit)
      (cleanStoredOutputBitSteps blocks)).map Configuration.outputBits = PMF.pure [bit] := by
  rw [cleanStoredOutputBit_eval, PMF.pure_map, cleanStoredOutputBitFinish_output]

/-- Unlike the standalone scratch rewind, the input boundary can be a bit
belonging to a retained request. The output separator controls the scan. -/
example :
    (rewindStoredGuessFinish [some true] [some false] (some false) [true, false] 3 2).inputTape =
      { left := [some false, some true], current := some true,
        right := [some false, none, none, none, none] } := by native_decide

example :
    (rewindStoredGuessFinish [some true] [some false] (some false) [] 3 2).inputTape =
      { left := [some false, some true], right := [none, none, none] } := by native_decide

example (before : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool) (inBlanks outBlanks : Nat) :
    (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart before boundary front back challenge bits inBlanks outBlanks)
      (finishStoredGuessSteps front back bits)).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) :=
  finishStoredGuess_evalResult before boundary front back challenge bits inBlanks outBlanks

/-- A malformed response is false before comparison. For a false challenge
it therefore returns true; the malformed branch is not forced to reject. -/
example :
    (evalConfigWithin (finishStoredGuess 3 2)
      (prepareStoredGuessStart [some true] (some false)
        [[], [false, true], []] [[true], []] false [true, false, true] 4 3)
      (finishStoredGuessSteps [[], [false, true], []] [[true], []] [true, false, true])).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [true]) := by
  simpa [taggedGuessValue] using finishStoredGuess_evalResult [some true] (some false)
    [[], [false, true], []] [[true], []] false [true, false, true] 4 3

example :
    (evalConfigWithin (finishStoredGuess 3 2)
      (prepareStoredGuessStart [some true] (some false)
        [[], [false, true], []] [[true], []] true [] 4 3)
      (finishStoredGuessSteps [[], [false, true], []] [[true], []] [])).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [false]) := by
  simpa [taggedGuessValue] using finishStoredGuess_evalResult [some true] (some false)
    [[], [false, true], []] [[true], []] true [] 4 3

example :
    (evalConfigWithin (finishStoredGuess 3 2)
      (prepareStoredGuessStart [some true] (some false)
        [[], [false, true], []] [[true], []] true [true, true] 4 3)
      (finishStoredGuessSteps [[], [false, true], []] [[true], []] [true, true])).map
        (fun c => (c.halted, c.outputBits)) = PMF.pure (true, [true]) := by
  simpa [taggedGuessValue] using finishStoredGuess_evalResult [some true] (some false)
    [[], [false, true], []] [[true], []] true [true, true] 4 3

example (front back : List (List Bool)) (bits : List Bool) :
    finishStoredGuessSteps front back bits ≤
      5 * bits.length + 4 * ((front.map List.length).sum + (back.map List.length).sum + front.length + back.length) + 33 :=
  finishStoredGuess_steps_le front back bits

/-- All retained guarded regions, including their encoded logical blank
cells, are charged by their actual contiguous physical block lengths. -/
example (request : List Bool) (input : Tape) :
    (storedSourceScratchBits request input).length = request.length + 2 * input.cells + 2 :=
  storedSourceScratchBits_length request input

example (before : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inBlanks outBlanks budget : Nat) (hFits : finishStoredGuessSteps front back bits ≤ budget) :
    (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart before boundary front back challenge bits inBlanks outBlanks)
      budget).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) :=
  finishStoredGuess_evalResult_of_le before boundary front back challenge bits inBlanks outBlanks budget hFits

end Foundation.Examples.StoredGuessCompletion
