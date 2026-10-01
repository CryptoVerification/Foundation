import Foundation.Constructions.ElGamal.MachineNormalization

namespace Machine.Examples

example : evalWithin readTaggedGuess [true, true] 7 =
    PMF.pure (some [true]) := readTaggedGuess_evalWithin _

example : evalWithin readTaggedGuess [true, false] 7 =
    PMF.pure (some [false]) := readTaggedGuess_evalWithin _

example : evalWithin readTaggedGuess [true, true, false] 7 =
    PMF.pure (some [false]) := readTaggedGuess_evalWithin _

example : evalWithin readTaggedGuess [false, true] 7 =
    PMF.pure (some [false]) := readTaggedGuess_evalWithin _

example : PolynomialTime readTaggedGuess := readTaggedGuess_polynomialTime

/-- The parser retains saved tape prefixes. No caller data are implicitly cleared. -/
example (beforeInput beforeOutput : List (Option Bool)) :
    RunsFor readTaggedGuess (readTaggedGuessStart beforeInput beforeOutput [true, true])
      (readTaggedGuessFinish beforeInput beforeOutput [true, true]) 7 :=
  readTaggedGuess_runs _ _ _

example (input : Tape) (saved : List (Option Bool)) :
    RunsFor matchPreviousOutputBit (matchPreviousOutputBitStart input saved true false)
      (matchPreviousOutputBitFinish input saved true false) 6 :=
  matchPreviousOutputBit_runs _ _ _ _

example (input : Tape) (saved : List (Option Bool)) :
    (matchPreviousOutputBitFinish input saved true false).outputTape =
      { left := saved, current := some false, right := [none] } := rfl

/-- Rejection of a malformed guess denotes false. A saved false challenge
therefore yields a true DDH comparison result, exactly as in Phase 11. -/
example (beforeInput : List (Option Bool)) :
    (evalConfigWithin finishTaggedGuess (finishTaggedGuessStart beforeInput [] false []) 10).map
      Configuration.outputBits = PMF.pure [true] :=
  ElGamal.finishTaggedGuess_correct FiniteBitEncoding.bool beforeInput false []

example (beforeInput : List (Option Bool)) :
    (evalConfigWithin finishTaggedGuess
      (finishTaggedGuessStart beforeInput [] true [true, true]) 14).map
      Configuration.outputBits = PMF.pure [true] :=
  ElGamal.finishTaggedGuess_correct FiniteBitEncoding.bool beforeInput true [true, true]

example (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (challenge : Bool) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre finishTaggedGuess suffix returnPc)
      ((finishTaggedGuessStart beforeInput beforeOutput challenge bits).rebasePc pre.length)
      (readTaggedGuessBudget bits + 7) =
      PMF.pure ((finishTaggedGuessFinish beforeInput beforeOutput challenge bits).resumeAt returnPc) :=
  finishTaggedGuess_withSubroutine_eval _ _ _ _ _ _ _

end Machine.Examples
