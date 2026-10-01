import Foundation.Machine.GuessCompletion

namespace Foundation.Examples.GuessCompletion

open Machine Machine.GuardedCompiler

/-- A genuine randomized tagged reply: write the tag, then write one fair
random bit and halt. Its finite code does not depend on the request. -/
def randomTaggedGuess : Program :=
  [.write .output true, .moveRight .output, .randomBit .output, .halt]

theorem randomTaggedGuess_haltsWithin (input : List Bool) :
    HaltsWithin randomTaggedGuess input 4 := by
  rw [haltsWithin_iff_reachableStates]
  intro c hc
  simp [reachableStates, paddedSuccessors, successors, next, randomTaggedGuess,
    Configuration.initial, Instruction.next, Configuration.advance, Configuration.updateTape] at hc
  rcases hc with rfl | rfl <;> rfl

example : (completedGuessFromProductCompile randomTaggedGuess).length = 957 := by
  rw [completedGuessFromProductCompile_length]
  rfl

/-- Retained source input from the actual multiplication-result layout,
with empty public payloads. Empty blocks remain physical separators. -/
def demoSavedInput : List (Option Bool) :=
  let original := encodeSecurityParameter 0 ++ frame [] ++
    frame (FiniteBitEncoding.delimit [] ++ FiniteBitEncoding.delimit [] ++ [])
  none :: (canonicalMessageBits [] [] []).reverse.map some ++
    none :: none :: original.reverse.map some ++ [none]

def demoProductReturn (challenge : Bool) : Configuration :=
  returnedFrameResult [.halt] []
    (none :: none :: none :: some challenge ::
      savedOutputBlocks (storedGuessBackBlocks [] [] {} {})) demoSavedInput {}

def demoBudget : Nat :=
  guessFromProductBudget (fun _ => 4) 0 [] [] [] [] [] [] [] [] [] [] +
    (completedGuessTerminalBudget (fun _ => 4) (guessFromProductRequest 0 [] [] [] []) [] [] []
      (true :: (FiniteBitEncoding.delimit [] ++ FiniteBitEncoding.delimit [] ++ [])) [] {} {} {} + 1)

/-- The full native wrapper starts from the retained multiply return and
uses the real randomized source distribution. The final source configuration
is not replaced by a separately supplied response bitstring. -/
example (challenge : Bool) :
    (evalConfigWithin (completedGuessFromProductCompile randomTaggedGuess)
      ((demoProductReturn challenge).resumeAt 0) demoBudget).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4).map
        (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  simpa [demoProductReturn, demoSavedInput, demoBudget, Configuration.outputBits,
    Tape.bits, List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] using
    completedGuessFromProductCompile_returnedFrameResult_evalResult [.halt] randomTaggedGuess
      (fun _ => 4) [] [] [] [] 0 [] [] [] [] [] [] [] [] [] challenge {} {} {}
      (randomTaggedGuess_haltsWithin _)

example (challenge : Bool) (c : Configuration)
    (run : PaddedRunsFor (completedGuessFromProductCompile randomTaggedGuess)
      ((demoProductReturn challenge).resumeAt 0) c demoBudget) : c.halted = true := by
  have h := completedGuessFromProductCompile_returnedFrameResult_haltsFrom [.halt] randomTaggedGuess
    (fun _ => 4) [] [] [] [] 0 [] [] [] [] [] [] [] [] [] challenge {} {} {}
    (randomTaggedGuess_haltsWithin _)
  simpa [demoProductReturn, demoSavedInput, demoBudget, Configuration.outputBits,
    Tape.bits, List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] using h c run

end Foundation.Examples.GuessCompletion
