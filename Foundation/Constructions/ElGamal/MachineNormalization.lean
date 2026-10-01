import Foundation.Constructions.ElGamal.MachinePrimitives
import Foundation.Constructions.ElGamal.MachineRepresented
import Foundation.Machine.GuardedGuess
import Foundation.Machine.NormalizedMessageSelection

namespace ElGamal

namespace RepresentedMachinePrimitives

/-- The arithmetic certificates constrain the element decoder only on
canonical encoded values. Replacing its behavior elsewhere preserves every
arithmetic program, budget, and correctness certificate. Consequently these
certificates alone do not justify native validation or normalization of an
arbitrary choose-stage machine output. -/
def withElementDecoder
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    (M : RepresentedMachinePrimitives sampling X embed)
    (decode : ∀ n (x : X n),
      List Bool → Option ((embed n x).params.Element))
    (hRoundTrip : ∀ n (x : X n) (a : (embed n x).params.Element),
      decode n x ((M.elementCode n x).encode a) = some a) :
    RepresentedMachinePrimitives sampling X embed :=
  { M with
    elementCode := fun n x =>
      { encode := (M.elementCode n x).encode,
        decode := decode n x,
        decode_encode := hRoundTrip n x } }

end RepresentedMachinePrimitives

/-- The mathematical choose-stage interpretation used by the existing
IND-CPA adapter. Invalid output or a guess-tagged response uses the default
messages and empty state. This function is a specification, not a machine
operation with zero cost. -/
def interpretChooseResponse {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α)
    (bits : List Bool) : α × α × List Bool :=
  match (responseCodeOfElement E).decode bits with
  | some (.inl messages) => messages
  | _ => (defaultMessage, defaultMessage, [])

/-- Canonical re-encoding of that interpretation. A native simulator must
implement this behavior on every finite raw source output, not just outputs
which were canonical element encodings already. -/
def normalizeChooseResponse {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α)
    (bits : List Bool) : List Bool :=
  (responseCodeOfElement E).encode
    (.inl (interpretChooseResponse E defaultMessage bits))


/-- The canonical specification has exactly the stored response layout read
by the native selector. This is an encoding identity, not a machine operation. -/
theorem normalizeChooseResponse_eq_canonical {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α) (bits : List Bool) :
    normalizeChooseResponse E defaultMessage bits = Machine.canonicalMessageBits
      (E.encode (interpretChooseResponse E defaultMessage bits).1)
      (E.encode (interpretChooseResponse E defaultMessage bits).2.1)
      (interpretChooseResponse E defaultMessage bits).2.2 := by
  simp [normalizeChooseResponse, responseCodeOfElement, Machine.FiniteBitEncoding.sum,
    Machine.FiniteBitEncoding.prod, Machine.FiniteBitEncoding.bitstring,
    Machine.canonicalMessageBits, List.append_assoc]

/-- The guess-stage interpretation is independent of the element decoder:
only a correctly tagged, exactly one-bit guess is accepted. -/
def interpretGuessResponse {α : Type}
    (E : Machine.FiniteBitEncoding α) (bits : List Bool) : Bool :=
  match (responseCodeOfElement E).decode bits with
  | some (.inr bit) => bit
  | _ => false

theorem interpretGuessResponse_eq_taggedGuessValue {α : Type}
    (E : Machine.FiniteBitEncoding α) (bits : List Bool) :
    interpretGuessResponse E bits = Machine.taggedGuessValue bits := by
  match bits with
  | [] => rfl
  | false :: rest =>
      simp only [interpretGuessResponse, responseCodeOfElement,
        Machine.FiniteBitEncoding.sum, Machine.taggedGuessValue]
      cases (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).decode rest <;> rfl
  | [true] => rfl
  | true :: bit :: rest =>
      cases rest with
      | nil => rfl
      | cons first tail => rfl

/-- Native guess normalization matches the existing abstract adapter on
every raw output, without any efficiency hypothesis about group decoding. -/
theorem readTaggedGuess_correct {α : Type}
    (E : Machine.FiniteBitEncoding α) (bits : List Bool) :
    Machine.evalWithin Machine.readTaggedGuess bits 7 =
      PMF.pure (some [interpretGuessResponse E bits]) := by
  rw [Machine.readTaggedGuess_evalWithin, interpretGuessResponse_eq_taggedGuessValue]

theorem normalizeChooseResponse_decode {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α) (bits : List Bool) :
    (responseCodeOfElement E).decode (normalizeChooseResponse E defaultMessage bits) =
      some (.inl (interpretChooseResponse E defaultMessage bits)) :=
  (responseCodeOfElement E).decode_encode _

/-- Re-encoding agrees with the source adapter on every raw output,
including invalid codes and wrong-stage responses. -/
theorem interpretChooseResponse_normalize {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α) (bits : List Bool) :
    interpretChooseResponse E defaultMessage (normalizeChooseResponse E defaultMessage bits) =
      interpretChooseResponse E defaultMessage bits := by
  unfold interpretChooseResponse
  rw [normalizeChooseResponse_decode]
  rfl

theorem interpretChooseResponse_state_length_le {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α) (bits : List Bool) :
    (interpretChooseResponse E defaultMessage bits).2.2.length ≤ bits.length := by
  cases h : (responseCodeOfElement E).decode bits with
  | none => simp [interpretChooseResponse, h]
  | some response =>
      cases response with
      | inl messages =>
          rcases messages with ⟨m₀, m₁, state⟩
          simpa [interpretChooseResponse, h] using
            responseCodeOfElement_state_length_le E bits m₀ m₁ state h
      | inr bit => simp [interpretChooseResponse, h]

/-- Canonicalization can retain at most the raw output's state length, plus
two uniformly bounded element codes and their delimiters. This is a size
lemma only; it does not supply the native canonicalization algorithm. -/
theorem normalizeChooseResponse_length_le {α : Type}
    (E : Machine.FiniteBitEncoding α) (defaultMessage : α)
    (elementLimit : Nat) (hElement : ∀ a, (E.encode a).length ≤ elementLimit)
    (bits : List Bool) :
    (normalizeChooseResponse E defaultMessage bits).length ≤
      4 * elementLimit + bits.length + 3 := by
  have hState := interpretChooseResponse_state_length_le E defaultMessage bits
  have hFirst := hElement (interpretChooseResponse E defaultMessage bits).1
  have hSecond := hElement (interpretChooseResponse E defaultMessage bits).2.1
  simp only [normalizeChooseResponse, responseCodeOfElement,
    Machine.FiniteBitEncoding.sum, Machine.FiniteBitEncoding.prod,
    Machine.FiniteBitEncoding.bitstring, List.length_cons, List.length_append,
    Machine.FiniteBitEncoding.delimit_length, id]
  omega

/-- Additional computational representation evidence needed for the current
element-based IND-CPA adapter: one fixed finite machine canonicalizes an
arbitrary source output exactly as the adapter's choose stage interprets it.
The encoded current instance, parameter, and raw output are its entire input.
It must halt on all finite inputs, including malformed fields, within a
polynomial bound in their total length. This is a local normalization
certificate, not a two-stage simulator or a claim that such a certificate
follows from the arithmetic primitives. No family is supplied to the code. -/
structure RepresentedChooseNormalizer
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    (M : RepresentedMachinePrimitives sampling X embed) where
  program : Machine.Program
  budget : Nat → Nat
  budget_polynomial : PolynomiallyBounded budget
  halts : ∀ input : List Bool,
    Machine.HaltsWithin program input (budget input.length)
  correct : ∀ n (x : X n) (bits : List Bool),
    let input := Machine.encodeSecurityParameter n ++
      Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame bits
    Machine.evalWithin program input (budget input.length) =
      PMF.pure (some (normalizeChooseResponse (M.elementCode n x)
        (embed n x).params.generator bits))

namespace RepresentedChooseNormalizer

theorem polynomialTime
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) : Machine.PolynomialTime N.program :=
  ⟨N.budget, N.budget_polynomial, N.halts⟩


/-- Every actual normalizer branch at its certified stopping budget has the
canonical output, including when the original choose response was malformed.
The support premise refers to the native source execution distribution. -/
theorem preparedBranch_output
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) (n : Nat) (x : X n) (rawReply : List Bool)
    (c : Machine.Configuration)
    (hc : c ∈ (Machine.evalConfigWithin N.program
      (Machine.GuardedCompiler.preparedSource (Machine.encodeSecurityParameter n ++
        Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply))
      (N.budget (Machine.encodeSecurityParameter n ++
        Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply).length)).support) :
    c.outputBits = normalizeChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply := by
  let input := Machine.encodeSecurityParameter n ++
    Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply
  have hHalted := Machine.GuardedCompiler.preparedSource_all_branches_halted N.program
    input (N.budget input.length) (N.halts input) c
    ((Machine.mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hMem : (if c.halted then some c.outputBits else none) ∈
      (Machine.evalWithin N.program input (N.budget input.length)).support := by
    rw [← Machine.GuardedCompiler.preparedSource_evalOutput, PMF.mem_support_map_iff]
    exact ⟨c, hc, rfl⟩
  change (if c.halted then some c.outputBits else none) ∈
    (Machine.evalWithin N.program (Machine.encodeSecurityParameter n ++
      Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply)
      (N.budget input.length)).support at hMem
  rw [N.correct n x rawReply] at hMem
  have hEq : some c.outputBits = some (normalizeChooseResponse (M.elementCode n x)
      (embed n x).params.generator rawReply) := by
    simpa only [hHalted, ↓reduceIte, PMF.mem_support_pure_iff] using hMem
  exact Option.some.inj hEq

/-- Actual native selection/copy from a returned certified normalizer branch.
The fair bit is sampled by machine code; the chosen element code is copied
from the same stored canonical response. Caller prefixes and normalizer
scratch are preserved and no new initialized tape is supplied. -/
theorem nativeBranch_selectMessage
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) (n : Nat) (x : X n) (rawReply : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Machine.Configuration)
    (hc : c ∈ (Machine.evalConfigWithin N.program
      (Machine.GuardedCompiler.preparedSource (Machine.encodeSecurityParameter n ++
        Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply))
      (N.budget (Machine.encodeSecurityParameter n ++
        Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply).length)).support) :
    let input := Machine.encodeSecurityParameter n ++ Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame rawReply
    let messages := interpretChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply
    let first := (M.elementCode n x).encode messages.1
    let second := (M.elementCode n x).encode messages.2.1
    let returned := (Machine.GuardedCompiler.rawResultFrom N.program input beforeInput (none :: savedInput) c).swapTapes
    Machine.evalConfigWithin Machine.prepareSelectedMessage (returned.resumeAt 0)
      (Machine.prepareSelectedMessageSteps first second messages.2.2) =
      Foundation.Probability.sampleBit.map (Machine.prepareSelectedMessageFinish savedInput returned.outputTape.left
        first second messages.2.2 (2 * c.outputTape.cells + 2 - c.outputBits.length)) := by
  dsimp only
  apply Machine.GuardedCompiler.selectNormalizedMessage_eval
  rw [N.preparedBranch_output n x rawReply c hc, normalizeChooseResponse_eq_canonical]


/-- The entire native rewind/select/copy stage has a linear step bound in
the supplied uniform element-code limit and actual raw response length.
The raw state retained by normalization cannot exceed that response length. -/
theorem nativeSelection_steps_le
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (n : Nat) (x : X n) (rawReply : List Bool) :
    let messages := interpretChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply
    Machine.prepareSelectedMessageSteps ((M.elementCode n x).encode messages.1)
      ((M.elementCode n x).encode messages.2.1) messages.2.2 ≤
      56 * M.elementCodeLength n + 14 * rawReply.length + 69 := by
  let messages := interpretChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply
  have hSteps := Machine.prepareSelectedMessage_steps_le ((M.elementCode n x).encode messages.1)
    ((M.elementCode n x).encode messages.2.1) messages.2.2
  have hSize := normalizeChooseResponse_length_le (M.elementCode n x) (embed n x).params.generator
    (M.elementCodeLength n) (M.elementCode_length_le n x) rawReply
  rw [normalizeChooseResponse_eq_canonical] at hSize
  change (Machine.canonicalMessageBits ((M.elementCode n x).encode messages.1)
    ((M.elementCode n x).encode messages.2.1) messages.2.2).length ≤
      4 * M.elementCodeLength n + rawReply.length + 3 at hSize
  change Machine.prepareSelectedMessageSteps ((M.elementCode n x).encode messages.1)
    ((M.elementCode n x).encode messages.2.1) messages.2.2 ≤ _
  omega

/-- The supplied normalization certificate is now invoked by a finite
native continuation which prepares its input from stored DDH cells and the
actual raw choose response. The observed input tape still contains the
saved DDH input, raw response, and canonical response in that order.
This is one simulator stage, not the complete challenge/guess wrapper. -/
theorem nativeContinuation_correct
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) (savedOutput : List (Option Bool))
    (n : Nat) (x : X n) (bit : Bool) (tupleTail rawReply : List Bool) (blanks : Nat) :
    (Machine.evalConfigWithin (Machine.GuardedCompiler.normalizeChooseCompile N.program)
      (Machine.prepareChooseNormalizationStart savedOutput n ((M.instanceCode n).encode x)
        bit tupleTail rawReply blanks)
      (Machine.GuardedCompiler.normalizationTraceBudget N.budget n ((M.instanceCode n).encode x)
        (bit :: tupleTail) rawReply)).map (fun c => (c.halted, c.inputTape.bits)) =
      PMF.pure (true, Machine.encodeSecurityParameter n ++ Machine.frame ((M.instanceCode n).encode x) ++
        Machine.frame (bit :: tupleTail) ++ rawReply ++
        normalizeChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply) := by
  rw [Machine.GuardedCompiler.normalizeChooseCompile_evalOutput N.program savedOutput n
    ((M.instanceCode n).encode x) bit tupleTail rawReply blanks N.budget (N.halts _),
    N.correct n x rawReply, PMF.pure_map]
  rfl

end RepresentedChooseNormalizer

/-- Native DDH final output agrees with the existing IND-CPA guess fallback
and comparison with the saved challenge. Invalid guess output denotes false;
it must still be compared with the challenge, rather than forcing a false
DDH result. -/
theorem finishTaggedGuess_correct {α : Type}
    (E : Machine.FiniteBitEncoding α) (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) :
    (Machine.evalConfigWithin Machine.finishTaggedGuess
      (Machine.finishTaggedGuessStart beforeInput [] challenge bits)
      (Machine.readTaggedGuessBudget bits + 7)).map
        Machine.Configuration.outputBits =
      PMF.pure [interpretGuessResponse E bits == challenge] := by
  rw [Machine.finishTaggedGuess_eval]
  simp only [PMF.map, PMF.pure_bind, Function.comp_apply, Machine.finishTaggedGuessFinish_outputBits,
    interpretGuessResponse_eq_taggedGuessValue]

/-- Native cleanup from a returned source branch, with no fresh tape load.
The output copy is erased by machine steps, the input copy is rewound, and
the original guess interpretation is compared with the saved challenge. -/
theorem finishCopiedGuess_correct {α : Type}
    (E : Machine.FiniteBitEncoding α) (source : Machine.Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (c : Machine.Configuration) :
    (Machine.evalConfigWithin Machine.finishCopiedGuess
      ((Machine.GuardedCompiler.rawResultFrom source input beforeInput [some challenge] c).resumeAt 0)
      (Machine.finishCopiedGuessSteps c.outputBits)).map (fun d => (d.halted, d.outputBits)) =
      PMF.pure (true, [interpretGuessResponse E c.outputBits == challenge]) := by
  rw [interpretGuessResponse_eq_taggedGuessValue]
  exact Machine.finishCopiedGuess_rawResult_eval source input beforeInput challenge c

/-- The entire compiled guess call preserves the existing adapter's meaning,
including its false fallback on malformed raw output. Native source steps,
result cleanup, tagged parsing, comparison, and the caller halt are charged.
This proves the final simulator stage; it does not construct its choose or
ciphertext-preparation stages. -/
theorem guessCompile_correct {α : Type}
    (E : Machine.FiniteBitEncoding α) (source : Machine.Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (q : Nat → Nat)
    (halts : Machine.HaltsWithin source input (q input.length)) :
    (Machine.evalConfigWithin (Machine.GuardedCompiler.guessCompile source)
      (Machine.GuardedCompiler.packInputStart beforeInput [some challenge] input)
      (Machine.GuardedCompiler.guessTraceBudget q input.length)).map Machine.Configuration.outputBits =
      (Machine.evalWithin source input (q input.length)).map
        (fun output => [(match output with
          | some bits => interpretGuessResponse E bits
          | none => false) == challenge]) := by
  rw [Machine.GuardedCompiler.guessCompile_evalOutput source input beforeInput challenge q halts]
  congr 1
  funext output
  cases output with
  | none => rfl
  | some bits =>
      change [Machine.taggedGuessValue bits == challenge] = [interpretGuessResponse E bits == challenge]
      rw [interpretGuessResponse_eq_taggedGuessValue]

end ElGamal
