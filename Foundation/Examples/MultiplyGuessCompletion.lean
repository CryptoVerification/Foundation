import Foundation.Machine.MultiplyGuessCompletion
import Foundation.Examples.GuessCompletion

namespace Foundation.Examples.MultiplyGuessCompletion

open Machine Machine.GuardedCompiler
open Foundation.Examples.GuessCompletion

example : (multiplyThenGuessCompile [.halt] randomTaggedGuess).length = 1251 := by
  rw [multiplyThenGuessCompile_length]
  rfl

example : (operandsMultiplyGuessCompile [.halt] randomTaggedGuess).length = 1367 := by
  rw [operandsMultiplyGuessCompile_length]
  rfl

private theorem emptyResult_correct (input : List Bool) :
    evalWithin [.halt] input 1 = PMF.pure (some []) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next, Configuration.initial,
    Configuration.outputBits, Tape.bits, PMF.pure_map, PMF.pure_bind]

def demoMultiplyRequest : List Bool := encodeSecurityParameter 0 ++ frame [] ++ frame [] ++ frame []

def demoStart (challenge : Bool) : Configuration :=
  (prepareMultiplyOperandsFinish []
    (some challenge :: savedOutputBlocks (storedGuessBackBlocks [] [] {} {})) [] 0
    [] [] [] [] [] (canonicalMessageBits [] [] []) []).resumeAt 0

def demoTailBudget : Nat :=
  multiplyGuessTailBudget (fun _ => 1) (fun _ => 4) demoMultiplyRequest [] [] 0
    [] [] [] [] [] [] [] [] [] [] {} {}

def demoBudget : Nat :=
  storedFramedCallTraceBudget (fun _ => 1) [] [] (canonicalMessageBits [] [] []) [] demoMultiplyRequest +
    (demoTailBudget + 1)

/-- The empty-result call is a protocol test, not a cryptographic multiplication
claim. The same native wrapper executes that call, then a genuine randomized
tagged guess, and returns exactly its comparison with the saved challenge. -/
example (challenge : Bool) :
    (evalConfigWithin (multiplyThenGuessCompile [.halt] randomTaggedGuess) (demoStart challenge) demoBudget).map
      (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4).map
        (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  exact multiplyThenGuessCompile_correct [.halt] randomTaggedGuess (fun _ => 1) (fun _ => 4)
    [] [] [] 0 [] [] [] [] [] [] [] [] [] [] challenge {} {} 0
    (haltInstruction_haltsWithin _) (emptyResult_correct _) (randomTaggedGuess_haltsWithin _)

example (challenge : Bool) (c : Configuration)
    (run : PaddedRunsFor (multiplyThenGuessCompile [.halt] randomTaggedGuess) (demoStart challenge) c demoBudget) :
    c.halted = true := by
  exact multiplyThenGuessCompile_correct_haltsFrom [.halt] randomTaggedGuess (fun _ => 1) (fun _ => 4)
    [] [] [] 0 [] [] [] [] [] [] [] [] [] [] challenge {} {} 0
    (haltInstruction_haltsWithin _) (emptyResult_correct _) (randomTaggedGuess_haltsWithin _) c run

/-- Starting before operand restoration charges its native rewinds and
framing too. This continuation still emits the same final output PMF. -/
example (challenge : Bool) :
    (evalConfigWithin (operandsMultiplyGuessCompile [.halt] randomTaggedGuess)
      (prepareMultiplyOperandsStart []
        (some challenge :: savedOutputBlocks (storedGuessBackBlocks [] [] {} {})) [] 0
        [] [] [] [] [] (canonicalMessageBits [] [] []) [])
      (prepareMultiplyOperandsSteps 0 [] [] [] [] [] (canonicalMessageBits [] [] []) [] + (demoBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4).map
        (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  exact operandsMultiplyGuessCompile_correct [.halt] randomTaggedGuess (fun _ => 1) (fun _ => 4)
    [] [] [] 0 [] [] [] [] [] [] [] [] [] [] challenge {} {} 0
    (haltInstruction_haltsWithin _) (emptyResult_correct _) (randomTaggedGuess_haltsWithin _)

end Foundation.Examples.MultiplyGuessCompletion
