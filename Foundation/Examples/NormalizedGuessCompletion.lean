import Foundation.Machine.NormalizedGuessCompletion
import Foundation.Examples.GuessCompletion
import Foundation.Constructions.ElGamal.Concrete

namespace Foundation.Examples.NormalizedGuessCompletion

open Machine Machine.GuardedCompiler
open Foundation.Examples.GuessCompletion

example : (selectedMultiplyGuessCompile [.halt] randomTaggedGuess).length = 1520 := by
  rw [selectedMultiplyGuessCompile_length]
  rfl

example : (normalizedMultiplyGuessCompile [.halt] randomTaggedGuess).length = 1570 := by
  rw [normalizedMultiplyGuessCompile_length]
  rfl

private theorem emptyResult_correct (input : List Bool) :
    evalWithin [.halt] input 1 = PMF.pure (some []) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next, Configuration.initial,
    Configuration.outputBits, Tape.bits, PMF.pure_map, PMF.pure_bind]

def message₀ : List Bool := [true]
def message₁ : List Bool := [false, true]
def state : List Bool := [true, false]

def demoOriginal : List Bool :=
  encodeSecurityParameter 2 ++ frame [false] ++ true :: multiplyTupleTail [true] [false, true] [true, false]

def demoSaved : List (Option Bool) :=
  [true, false].reverse.map some ++ none :: demoOriginal.reverse.map some ++ [none, some false]

def demoBack : List (Option Bool) := savedOutputBlocks (storedGuessBackBlocks [] [] {} {})

def demoStart : Configuration := prepareMessageSelectionStart demoSaved demoBack message₀ message₁ state 17

def demoTailBudget : Nat :=
  normalizedMultiplyGuessTailBudget (fun _ => 1) (fun _ => 4) [] [] 2
    [false] [true] [false, true] [true, false] [true, false] message₀ message₁ state (fun _ => []) {} {}

def demoBudget : Nat := prepareSelectedMessageSteps message₀ message₁ state + (demoTailBudget + 1)

/-- The halting empty-output call is only a protocol test. The messages have
different lengths, so the two actual continuation requests differ; a common
budget covers both native challenge choices and the randomized tagged guess. -/
theorem demo_eval :
    (evalConfigWithin (normalizedMultiplyGuessCompile [.halt] randomTaggedGuess) demoStart demoBudget).map
      (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 2 [false] [false, true] state [])) 4).map
          (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  exact normalizedMultiplyGuessCompile_correct [.halt] randomTaggedGuess (fun _ => 1) (fun _ => 4)
    [] [] [some false] 2 [false] [true] [false, true] [true, false] [true, false] message₀ message₁ state
    (fun _ => []) {} {} 17 (fun _ => haltInstruction_haltsWithin _)
    (fun _ => emptyResult_correct _) (fun _ => randomTaggedGuess_haltsWithin _)

/-- Reuse the Phase 11 independent-guess probability theorem: although the
actual native wrapper runs both random instructions and all tape stages,
this protocol test's final success bit is fair. -/
example :
    (evalConfigWithin (normalizedMultiplyGuessCompile [.halt] randomTaggedGuess) demoStart demoBudget).map
      (fun c => (c.halted, c.outputBits)) =
        Foundation.Probability.sampleBit.map (fun bit => (true, [bit])) := by
  rw [demo_eval]
  let source := evalConfigWithin randomTaggedGuess
    (preparedSource (guessFromProductRequest 2 [false] [false, true] state [])) 4
  have h := congrArg (fun law : PMF Bool => law.map (fun bit => (true, [bit])))
    (ElGamal.independentGuess_game_eq (source.map (fun c => taggedGuessValue c.outputBits)))
  change (Foundation.Probability.sampleBit.bind fun bit =>
    source.bind (fun c => PMF.pure (true, [taggedGuessValue c.outputBits == bit]))) = _
  simpa only [PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def] using h

example (c : Configuration)
    (run : PaddedRunsFor (normalizedMultiplyGuessCompile [.halt] randomTaggedGuess) demoStart c demoBudget) :
    c.halted = true := by
  exact normalizedMultiplyGuessCompile_correct_haltsFrom [.halt] randomTaggedGuess (fun _ => 1) (fun _ => 4)
    [] [] [some false] 2 [false] [true] [false, true] [true, false] [true, false] message₀ message₁ state
    (fun _ => []) {} {} 17 (fun _ => haltInstruction_haltsWithin _)
    (fun _ => emptyResult_correct _) (fun _ => randomTaggedGuess_haltsWithin _) c run

-- Either selected-message budget is bounded by the single actual execution
-- budget; there is no choice of a shorter successful random branch.
example (bit : Bool) :
    selectedMultiplyGuessBudget (fun _ => 1) (fun _ => 4) [] [] 2
      [false] [true] [false, true] [true, false] [true, false] message₀ message₁ state [] bit {} {} ≤ demoTailBudget :=
  normalizedMultiplyGuessTailBudget_fits (fun _ => 1) (fun _ => 4) [] [] 2
    [false] [true] [false, true] [true, false] [true, false] message₀ message₁ state (fun _ => []) {} {} bit

end Foundation.Examples.NormalizedGuessCompletion
