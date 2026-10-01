import Foundation.Constructions.ElGamal.MachineNormalization

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

end Machine.Examples
