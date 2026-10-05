import Foundation.Crypto.Semantics.Machine.GuessCompletion

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

-- Missing separators in the saved output prefix do not prevent a native
-- rewind and guarded source call. This source really uses a random bit;
-- the stopping theorem covers both branches of the call.
example (inputBlanks outputBlanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor (storedGuessCallCompile randomTaggedGuess)
      ({ inputTape := { left := [some false], right := List.replicate inputBlanks none },
         outputTape := { left := [some true, some false, some true], right := List.replicate outputBlanks none } } : Configuration)
      finish (storedGuessFreshBudget 4 0
        (sourceStorage {
          inputTape := { left := [some false], right := List.replicate inputBlanks none },
          outputTape := { left := [some true, some false, some true], right := List.replicate outputBlanks none } }))) :
    finish.halted = true := by
  exact storedGuessCallCompile_haltsFrom_fresh_tapes randomTaggedGuess 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ _ _ finish run

-- The complete construction-and-call stage accepts arbitrary retained
-- strings. No validity premise is added to the generic stopping theorem.
example (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∀ finish, PaddedRunsFor (guessFromProductCompile randomTaggedGuess) start finish
      (guessRetainedBudget 4 0 (sourceStorage start)) → finish.halted = true :=
  guessFromProductCompile_haltsFrom_retained_frontiers randomTaggedGuess 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ _ _ _ _ _ _ _

example : PolynomiallyBounded (storedGuessFreshBudget 4 0) :=
  storedGuessFreshBudget_polynomial _ _

example : PolynomiallyBounded (guessRetainedBudget 4 0) :=
  guessRetainedBudget_polynomial _ _

-- The final processor needs neither a valid tagged reply nor a matching
-- reply copy. Every finite pair of tapes has the same charged stopping bound.
example (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor (finishStoredGuess 8 4)
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (4500000000 * (output.cells + 1))) : finish.halted = true :=
  finishStoredGuess_haltsFrom_anyTape 8 4 input output finish run

-- The whole construction, randomized source invocation, and final cleanup
-- now stop on arbitrary retained strings, including malformed replies.
example (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∀ finish, PaddedRunsFor (completedGuessFromProductCompile randomTaggedGuess) start finish
      (completedGuessRetainedBudget 4 0 (sourceStorage start)) → finish.halted = true :=
  completedGuessFromProductCompile_haltsFrom_retained_frontiers randomTaggedGuess 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ _ _ _ _ _ _ _

example : PolynomiallyBounded (completedGuessRetainedBudget 4 0) :=
  completedGuessRetainedBudget_polynomial _ _

-- The actual multiplication return can contain any raw product and any
-- retained public/reply strings. Its physical tapes, including the source
-- scratch, are passed directly to the full randomized guess continuation.
example (multiplyRequest : List Bool) (beforeOutput before : List (Option Bool))
    (original reply canonical selected : List Bool) (multiplyResult : Configuration) :
    let saved := selected.reverse.map some ++ none :: canonical.reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := returnedFrameResult [.halt] multiplyRequest beforeOutput saved multiplyResult
    ∀ finish, PaddedRunsFor (completedGuessFromProductCompile randomTaggedGuess) (returned.resumeAt 0) finish
      (completedGuessRetainedBudget 4 0 (sourceStorage returned)) → finish.halted = true :=
  completedGuessFromProductCompile_returnedFrameResult_haltsFrom_retained [.halt] randomTaggedGuess 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ _ _ _ _ _ _

end Foundation.Examples.GuessCompletion
