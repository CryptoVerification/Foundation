import Foundation.Machine.NormalizationGuessCompletion
import Foundation.Examples.GuessCompletion

namespace Foundation.Examples.NormalizationGuessCompletion

open Machine Machine.GuardedCompiler
open Foundation.Examples.GuessCompletion

/-- A finite native normalizer for this protocol fixture only: emit the
three empty delimited fields by six actual bit-machine transitions. -/
def emptyNormalizer : Program :=
  [.write .output false, .moveRight .output, .write .output false,
    .moveRight .output, .write .output false, .halt]

theorem emptyNormalizer_haltsWithin (input : List Bool) :
    HaltsWithin emptyNormalizer input 6 := by
  rw [haltsWithin_iff_reachableStates]
  intro c hc
  simp [reachableStates, paddedSuccessors, successors, next, emptyNormalizer,
    Configuration.initial, Instruction.next, Configuration.advance, Configuration.updateTape] at hc
  subst c
  rfl

theorem emptyNormalizer_correct (input : List Bool) :
    evalWithin emptyNormalizer input 6 = PMF.pure (some (canonicalMessageBits [] [] [])) := by
  simp [emptyNormalizer, evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
    Configuration.initial, Configuration.outputBits, Configuration.advance, Configuration.updateTape,
    Tape.bits, Tape.write, Tape.moveRight, canonicalMessageBits, FiniteBitEncoding.delimit,
    PMF.pure_map, PMF.pure_bind]

private theorem emptyResult_correct (input : List Bool) :
    evalWithin [.halt] input 1 = PMF.pure (some []) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next, Configuration.initial,
    Configuration.outputBits, Tape.bits, PMF.pure_map, PMF.pure_bind]

def demoStart : Configuration :=
  prepareChooseNormalizationStart
    ((rawResultFrom [.halt] [] [none] [] {}).swapTapes).outputTape.left
    0 [] false [false] [] 8

def demoTailBudget : Nat :=
  normalizationChallengeTailBudget (fun _ => 6) (fun _ => 1) (fun _ => 4)
    [] 0 [] [] [] [] [] [] [] [] (fun _ => []) {}

def demoBudget : Nat := normalizationTraceBudget (fun _ => 6) 0 [] [false, false] [] + (demoTailBudget + 1)

example : (normalizationChallengeGuessCompile emptyNormalizer [.halt] randomTaggedGuess).length = 2233 := by
  rw [normalizationChallengeGuessCompile_length]
  rfl

/-- The same native program calls the normalizer, draws a challenge bit,
performs the empty-result protocol call and runs the genuinely randomized
guess. The halting multiplication fixture is not a group algorithm. -/
theorem demo_eval :
    (evalConfigWithin (normalizationChallengeGuessCompile emptyNormalizer [.halt] randomTaggedGuess)
      demoStart demoBudget).map (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4).map
          (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  exact normalizationChallengeGuessCompile_correct [.halt] emptyNormalizer [.halt] randomTaggedGuess
    (fun _ => 6) (fun _ => 1) (fun _ => 4) [] [] 0 [] [] [] [] [] [] [] []
    false [false] rfl (fun _ => []) {} 8 (emptyNormalizer_haltsWithin _)
    (emptyNormalizer_correct _) (fun _ => haltInstruction_haltsWithin _)
    (fun _ => emptyResult_correct _) (fun _ => randomTaggedGuess_haltsWithin _)

example (c : Configuration)
    (run : PaddedRunsFor (normalizationChallengeGuessCompile emptyNormalizer [.halt] randomTaggedGuess)
      demoStart c demoBudget) : c.halted = true := by
  exact normalizationChallengeGuessCompile_correct_haltsFrom [.halt] emptyNormalizer [.halt] randomTaggedGuess
    (fun _ => 6) (fun _ => 1) (fun _ => 4) [] [] 0 [] [] [] [] [] [] [] []
    false [false] rfl (fun _ => []) {} 8 (emptyNormalizer_haltsWithin _)
    (emptyNormalizer_correct _) (fun _ => haltInstruction_haltsWithin _)
    (fun _ => emptyResult_correct _) (fun _ => randomTaggedGuess_haltsWithin _) c run

end Foundation.Examples.NormalizationGuessCompletion
