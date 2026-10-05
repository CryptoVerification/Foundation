import Foundation.Constructions.ElGamal.MachinePrimitives
import Foundation.Crypto.Semantics.Machine.MultiplyCallPreparation
import Foundation.Crypto.Semantics.Machine.StoredCallInvocation
import Foundation.Crypto.Semantics.Machine.StoredFramedCall
import Foundation.Crypto.Semantics.Machine.MultiplyGuessCompletion
import Foundation.Crypto.Semantics.Machine.NormalizedGuessCompletion
import Foundation.Crypto.Semantics.Machine.NormalizationGuessCompletion
import Foundation.Constructions.ElGamal.MachineNormalization

namespace ElGamal

open Machine Machine.GuardedCompiler

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1}
  {embed : ∀ n, X n → ConcreteInstance sampling n}

/-- Execute the fixed represented multiplication program from the actual
returned operand-assembly configuration. Frontier scans, request rewind,
guarded execution, and final halt are all instructions of the wrapper.
The result is the code for `message * T`, in that order. -/
theorem RepresentedSimulatorPrimitives.nativeMultiplyFromOperands_eval
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (before savedOutput : List (Option Bool)) (n : Nat) (x : X n)
    (first second last message : (embed n x).params.Element)
    (reply canonical : List Bool) (blanks : Nat) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (E.encode message) ++ frame (E.encode last)
    let saved := none :: (E.encode message).reverse.map some ++ none :: canonical.reverse.map some ++
      none :: reply.reverse.map some ++ none :: (E.encode last).reverse.map some ++
        multiplyCallBeforeElement before n I (E.encode first) (E.encode second) (E.encode last)
    (evalConfigWithin (storedCallCompile M.multiplyProgram)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none) n I
        (E.encode first) (E.encode second) (E.encode last) reply canonical (E.encode message)).resumeAt 0)
      (storedCallTraceBudget M.multiplyBudget (E.encode last) reply canonical (E.encode message) request)).map
        (fun c => (c.halted, c.inputTape.bits.drop (saved.reverse.filterMap id).length)) =
      PMF.pure (true, E.encode ((embed n x).params.mul message last)) := by
  dsimp only
  rw [prepareMultiplyOperandsFinish_call_layout, storedCallCompile_evalResult,
    M.multiply_correct n x message last, PMF.pure_map]
  rfl
  exact M.multiplyHalts _

/-- Every random branch of the native represented call halts. The source
certificate is applied to this assembled request's actual finite length;
no monotonicity of its budget or meta-level instance oracle is assumed. -/
theorem RepresentedSimulatorPrimitives.nativeMultiplyFromOperands_halts
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (before savedOutput : List (Option Bool)) (n : Nat) (x : X n)
    (first second last message : (embed n x).params.Element)
    (reply canonical : List Bool) (blanks : Nat) (finish : Configuration) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (E.encode message) ++ frame (E.encode last)
    PaddedRunsFor (storedCallCompile M.multiplyProgram)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none) n I
        (E.encode first) (E.encode second) (E.encode last) reply canonical (E.encode message)).resumeAt 0)
      finish (storedCallTraceBudget M.multiplyBudget (E.encode last) reply canonical (E.encode message) request) →
      finish.halted = true := by
  dsimp only
  rw [prepareMultiplyOperandsFinish_call_layout]
  exact storedCallCompile_haltsFrom _ _ _ _ _ _ _ _ _ _ M.multiplyBudget (M.multiplyHalts _) finish

/-- After the actual operand preparation, native invocation and framing
place the frame of `message * T` in the physical output cells immediately
behind the head. The same execution retains the stored challenge, canonical
response, original tuple, and simulated multiplication scratch. -/
theorem RepresentedSimulatorPrimitives.nativeMultiplyFramedFromOperands_eval
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (before savedOutput : List (Option Bool)) (n : Nat) (x : X n)
    (first second last message : (embed n x).params.Element)
    (reply canonical : List Bool) (blanks : Nat) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let result := E.encode ((embed n x).params.mul message last)
    let request := encodeSecurityParameter n ++ frame I ++ frame (E.encode message) ++ frame (E.encode last)
    (evalConfigWithin (storedFramedCallCompile M.multiplyProgram)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none) n I
        (E.encode first) (E.encode second) (E.encode last) reply canonical (E.encode message)).resumeAt 0)
      (storedFramedCallTraceBudget M.multiplyBudget (E.encode last) reply canonical (E.encode message) request)).map
        (fun c => (c.halted, fun i : Fin (frame result).length => c.outputTape.left.getD i.val none)) =
      PMF.pure (true, fun i : Fin (frame result).length => ((frame result).reverse.map some).getD i.val none) := by
  dsimp only
  rw [prepareMultiplyOperandsFinish_call_layout]
  exact storedFramedCallCompile_evalFrameCells _ _ _ _ _ _ _ _ _ _ _ M.multiplyBudget
    (M.multiplyHalts _) (M.multiply_correct n x message last)

theorem RepresentedSimulatorPrimitives.nativeMultiplyFramedFromOperands_halts
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (before savedOutput : List (Option Bool)) (n : Nat) (x : X n)
    (first second last message : (embed n x).params.Element)
    (reply canonical : List Bool) (blanks : Nat) (finish : Configuration) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (E.encode message) ++ frame (E.encode last)
    PaddedRunsFor (storedFramedCallCompile M.multiplyProgram)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none) n I
        (E.encode first) (E.encode second) (E.encode last) reply canonical (E.encode message)).resumeAt 0)
      finish (storedFramedCallTraceBudget M.multiplyBudget (E.encode last) reply canonical (E.encode message) request) →
      finish.halted = true := by
  dsimp only
  rw [prepareMultiplyOperandsFinish_call_layout]
  exact storedFramedCallCompile_haltsFrom _ _ _ _ _ _ _ _ _ _ M.multiplyBudget (M.multiplyHalts _) finish

/-- Execute multiplication and the final guess in one native machine code.
The actual group-operation certificate determines the ciphertext second
component; the source guess call consumes that product on the retained tapes.
The common budget includes every multiplication scratch branch and the full
native finalization, rather than supplying a separate product bitstring. -/
theorem RepresentedSimulatorPrimitives.nativeMultiplyAndGuessFromOperands_eval
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (guessSource : Program) (qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat) (x : X n)
    (first second last message message₀ message₁ : (embed n x).params.Element)
    (reply state : List Bool) (challenge : Bool)
    (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hGuess : HaltsWithin guessSource
      (guessFromProductRequest n ((M.instanceCode n).encode x) ((M.elementCode n x).encode second) state
        ((M.elementCode n x).encode ((embed n x).params.mul message last)))
      (qGuess (guessFromProductRequest n ((M.instanceCode n).encode x) ((M.elementCode n x).encode second) state
        ((M.elementCode n x).encode ((embed n x).params.mul message last))).length)) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let product := E.encode ((embed n x).params.mul message last)
    let request := encodeSecurityParameter n ++ frame I ++ frame (E.encode message) ++ frame (E.encode last)
    let canonical := canonicalMessageBits (E.encode message₀) (E.encode message₁) state
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := multiplyGuessTailBudget M.multiplyBudget qGuess request chooseRequest normalizeRequest n
      I (E.encode first) (E.encode second) (E.encode last) reply (E.encode message₀) (E.encode message₁) state
      (E.encode message) product chooseResult normalizeResult
    (evalConfigWithin (multiplyThenGuessCompile M.multiplyProgram guessSource)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none) n I
        (E.encode first) (E.encode second) (E.encode last) reply canonical (E.encode message)).resumeAt 0)
      (storedFramedCallTraceBudget M.multiplyBudget (E.encode last) reply canonical (E.encode message) request +
        (tailBudget + 1))).map (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n I (E.encode second) state product))
        (qGuess (guessFromProductRequest n I (E.encode second) state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  exact multiplyThenGuessCompile_correct M.multiplyProgram guessSource M.multiplyBudget qGuess
    chooseRequest normalizeRequest before n ((M.instanceCode n).encode x)
    ((M.elementCode n x).encode first) ((M.elementCode n x).encode second) ((M.elementCode n x).encode last) reply
    ((M.elementCode n x).encode message₀) ((M.elementCode n x).encode message₁) state ((M.elementCode n x).encode message)
    ((M.elementCode n x).encode ((embed n x).params.mul message last)) challenge chooseResult normalizeResult blanks
    (M.multiplyHalts _) (M.multiply_correct n x message last) hGuess

/-- From the actual normalizer return, sample the challenge natively,
select its message, construct the multiplication request, invoke the fixed
group algorithm and source guess, and emit exactly one comparison bit.
The efficient multiplication certificate, rather than a free algebraic
primitive, supplies each branch's encoded ciphertext component. -/
theorem RepresentedSimulatorPrimitives.nativeChallengeAndGuessFromNormalizer_eval
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (chooseSource normalizeSource guessSource : Program) (qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (chooseSaved before : List (Option Bool))
    (n : Nat) (x : X n)
    (first second last message₀ message₁ : (embed n x).params.Element)
    (reply state : List Bool) (chooseResult normalizeResult : Configuration)
    (hOutput : normalizeResult.outputBits = canonicalMessageBits
      ((M.elementCode n x).encode message₀) ((M.elementCode n x).encode message₁) state)
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource
      (guessFromProductRequest n ((M.instanceCode n).encode x) ((M.elementCode n x).encode second) state
        ((M.elementCode n x).encode ((embed n x).params.mul (if bit then message₁ else message₀) last)))
      (qGuess (guessFromProductRequest n ((M.instanceCode n).encode x) ((M.elementCode n x).encode second) state
        ((M.elementCode n x).encode ((embed n x).params.mul (if bit then message₁ else message₀) last))).length)) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let product := fun bit : Bool => E.encode ((embed n x).params.mul (if bit then message₁ else message₀) last)
    let original := encodeSecurityParameter n ++ frame I ++
      true :: multiplyTupleTail (E.encode first) (E.encode second) (E.encode last)
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    let normalReturn := (rawResultFrom normalizeSource normalizeRequest (none :: chooseReturn.outputTape.left)
      (none :: saved) normalizeResult).swapTapes
    let tailBudget := normalizedMultiplyGuessTailBudget M.multiplyBudget qGuess chooseRequest normalizeRequest n I
      (E.encode first) (E.encode second) (E.encode last) reply (E.encode message₀) (E.encode message₁) state
      product chooseResult normalizeResult
    (evalConfigWithin (normalizedMultiplyGuessCompile M.multiplyProgram guessSource) (normalReturn.resumeAt 0)
      (prepareSelectedMessageSteps (E.encode message₀) (E.encode message₁) state + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n I (E.encode second) state (product bit)))
          (qGuess (guessFromProductRequest n I (E.encode second) state (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  apply normalizedMultiplyGuessCompile_fromNormalizer_correct chooseSource normalizeSource M.multiplyProgram guessSource
    M.multiplyBudget qGuess chooseRequest normalizeRequest chooseSaved before n ((M.instanceCode n).encode x)
    ((M.elementCode n x).encode first) ((M.elementCode n x).encode second) ((M.elementCode n x).encode last)
    reply ((M.elementCode n x).encode message₀) ((M.elementCode n x).encode message₁) state
    (fun bit : Bool => (M.elementCode n x).encode ((embed n x).params.mul (if bit then message₁ else message₀) last))
    chooseResult normalizeResult hOutput
  · intro bit
    exact M.multiplyHalts _
  · intro bit
    cases bit
    · exact M.multiply_correct n x message₀ last
    · exact M.multiply_correct n x message₁ last
  · exact hGuess

/-- The fixed normalizer is now executed by the same code as challenge
construction and the final guess. Its certificate covers arbitrary choose
replies, including malformed outputs, and supplies the canonical default
policy used by the existing adversary adapter. No normalizer branch or
encoded product is inserted into the caller's tapes mathematically. -/
theorem RepresentedChooseNormalizer.nativeNormalizeChallengeAndGuess_eval
    (M : RepresentedSimulatorPrimitives sampling X embed) (N : RepresentedChooseNormalizer M)
    (chooseSource guessSource : Program) (qGuess : Nat → Nat)
    (chooseRequest : List Bool) (chooseSaved : List (Option Bool)) (n : Nat) (x : X n)
    (first second last : (embed n x).params.Element) (reply : List Bool)
    (tupleBit : Bool) (tupleRest : List Bool)
    (hTuple : tupleBit :: tupleRest = FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
      FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last)
    (chooseResult : Configuration) (blanks : Nat)
    (hGuess : ∀ input, HaltsWithin guessSource input (qGuess input.length)) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let messages := interpretChooseResponse E (embed n x).params.generator reply
    let product := fun bit : Bool => E.encode ((embed n x).params.mul
      (if bit then messages.2.1 else messages.1) last)
    let tailBudget := normalizationChallengeTailBudget N.budget M.multiplyBudget qGuess chooseRequest n I
      (E.encode first) (E.encode second) (E.encode last) reply (E.encode messages.1) (E.encode messages.2.1)
      messages.2.2 product chooseResult
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    (evalConfigWithin (normalizationChallengeGuessCompile N.program M.multiplyProgram guessSource)
      (prepareChooseNormalizationStart chooseReturn.outputTape.left n I tupleBit tupleRest reply blanks)
      (normalizationTraceBudget N.budget n I (tupleBit :: tupleRest) reply + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n I (E.encode second) messages.2.2 (product bit)))
          (qGuess (guessFromProductRequest n I (E.encode second) messages.2.2 (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  apply normalizationChallengeGuessCompile_correct chooseSource N.program M.multiplyProgram guessSource
    N.budget M.multiplyBudget qGuess chooseRequest chooseSaved n ((M.instanceCode n).encode x)
    ((M.elementCode n x).encode first) ((M.elementCode n x).encode second) ((M.elementCode n x).encode last) reply
    ((M.elementCode n x).encode (interpretChooseResponse (M.elementCode n x) (embed n x).params.generator reply).1)
    ((M.elementCode n x).encode (interpretChooseResponse (M.elementCode n x) (embed n x).params.generator reply).2.1)
    (interpretChooseResponse (M.elementCode n x) (embed n x).params.generator reply).2.2
    tupleBit tupleRest hTuple
    (fun bit : Bool => (M.elementCode n x).encode ((embed n x).params.mul
      (if bit then (interpretChooseResponse (M.elementCode n x) (embed n x).params.generator reply).2.1
      else (interpretChooseResponse (M.elementCode n x) (embed n x).params.generator reply).1) last))
    chooseResult blanks
  · exact N.halts _
  · simpa only [normalizeChooseResponse_eq_canonical] using N.correct n x reply
  · intro bit
    exact M.multiplyHalts _
  · intro bit
    cases bit
    · exact M.multiply_correct n x _ last
    · exact M.multiply_correct n x _ last
  · intro bit
    exact hGuess _

end ElGamal
