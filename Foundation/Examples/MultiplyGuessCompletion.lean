import Foundation.Crypto.Semantics.Machine.MultiplyGuessCompletion
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

-- Two genuine randomized native calls share the retained physical tapes.
-- This is a stopping test, with no claim that the first call implements a
-- group operation. All saved strings, including malformed replies, are allowed.
example (before beforeOutput : List (Option Bool))
    (originalPrefix original reply canonical selected request : List Bool)
    (inputBlanks outputBlanks : Nat) :
    let start := prepareStoredCallStart (originalPrefix.reverse.map some ++ none :: before)
      beforeOutput original reply canonical selected request inputBlanks outputBlanks
    ∀ finish, PaddedRunsFor (multiplyThenGuessCompile randomTaggedGuess randomTaggedGuess) start finish
      (multiplyGuessRetainedBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true :=
  multiplyThenGuessCompile_haltsFrom_retained_frontiers randomTaggedGuess randomTaggedGuess 4 0 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ _ _ _ _ _ _ _ _

example : PolynomiallyBounded (multiplyGuessRetainedBudget 4 0 4 0) :=
  multiplyGuessRetainedBudget_polynomial _ _ _ _

-- The same theorem accepts the exact return of the existing operand
-- constructor. Its canonical-response slot is an arbitrary raw string;
-- no decoder or normalization correctness is needed for stopping here.
example (before savedOutput : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    let start := (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).resumeAt 0
    ∀ finish, PaddedRunsFor (multiplyThenGuessCompile randomTaggedGuess randomTaggedGuess) start finish
      (multiplyGuessRetainedBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true := by
  dsimp only
  rw [prepareMultiplyOperandsFinish_call_layout]
  let storedPublicPrefix := encodeSecurityParameter n ++ frame instanceBits ++
    encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length ++
    FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second
  have h := multiplyThenGuessCompile_haltsFrom_retained_frontiers randomTaggedGuess randomTaggedGuess 4 0 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    before (none :: selected.reverse.map some ++ none :: savedOutput) storedPublicPrefix last reply canonical selected
    (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
    blanks (instanceBits.length + 1 - (2 * last.length + 1))
  simpa only [storedPublicPrefix, List.reverse_append, List.map_append, List.append_assoc,
    List.cons_append, multiplyCallBeforeElement] using h

-- The head is already one cell into four raw retained blocks. No stored
-- field is required to decode as a DDH tuple or a canonical choose reply.
-- Both real calls are randomized, and the input has no caller separator
-- behind it. Only redundant outer blank equivalence is needed for the
-- complete guess continuation after the three new retained separators.
example :
    let input : Tape := {
      left := [some true]
      current := some false
      right := [none, some false, some false, none, some true, none, none] }
    let start : Configuration := { inputTape := input, outputTape := { left := [some false, some true, none] } }
    ∀ finish, PaddedRunsFor (multiplyThenGuessCompile randomTaggedGuess randomTaggedGuess) start finish
      (multiplyGuessRetainedSuffixBudget 4 0 4 0 (sourceStorage start)) → finish.halted = true := by
  dsimp only
  apply multiplyThenGuessCompile_haltsFrom_retained_suffix randomTaggedGuess randomTaggedGuess 4 0 4 0
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    (fun request => by simpa using randomTaggedGuess_haltsWithin request)
    _ _ 0 [true, false] [false, false] [true] [] 0 1
  intro i
  rfl

example : PolynomiallyBounded (multiplyGuessRetainedSuffixBudget 4 0 4 0) :=
  multiplyGuessRetainedSuffixBudget_polynomial _ _ _ _

end Foundation.Examples.MultiplyGuessCompletion
