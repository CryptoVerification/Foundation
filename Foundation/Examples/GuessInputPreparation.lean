import Foundation.Machine.GuessInvocationPreparation
import Foundation.Constructions.ElGamal.MachineRepresented
import Foundation.Examples.MachinePolynomialTime

namespace Machine.Examples

/-- The complete physical request agrees with the actual represented
ElGamal input format. The observation reads the cells already constructed
by the native machine; it does not load or frame a new request. -/
example {α : Type} (E : FiniteBitEncoding α) (y product : α)
    (before beforeOutput : List (Option Bool)) (n padding : Nat)
    (instanceBits first last reply message₀ message₁ state selected : List Bool) :
    (prepareGuessInputFinish before beforeOutput n instanceBits first (E.encode y) last reply
      message₀ message₁ state selected (E.encode product) padding).outputTape.left =
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame ((ElGamal.requestCodeOfElement E).encode (.inr (state, (y, product))))).reverse.map some ++
        none :: none ::
        ((ElGamal.requestCodeOfElement E).encode (.inr (state, (y, product)))).reverse.map some ++ none :: beforeOutput := by
  rw [prepareGuessInputFinish_output]
  simp [ElGamal.requestCodeOfElement, FiniteBitEncoding.sum, FiniteBitEncoding.prod,
    FiniteBitEncoding.bitstring, List.append_assoc]

/-- Empty payloads still have both ciphertext/state delimiters and an outer
frame. Caller data survive behind actual blank separators. -/
example (before beforeOutput : List (Option Bool)) :
    (prepareGuessInputFinish before beforeOutput 2 [false] [true] [false] [true]
      [false] [] [true] [] [] [] 7).outputTape.left =
      (encodeSecurityParameter 2 ++ frame [false] ++ frame [true, false, true, false, false]).reverse.map some ++
        none :: none :: [some false, some false, some true, some false, some true] ++ none :: beforeOutput := by
  rw [prepareGuessInputFinish_output]
  rfl

/-- Both tapes contain nonempty saved caller data and the input has explicit
outer padding. Complete body construction and outer framing run together. -/
example (before beforeOutput : List (Option Bool)) :
    evalConfigWithin prepareGuessInput
      (prepareGuessInputStart before beforeOutput 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true] 9)
      (prepareGuessInputSteps 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true]) =
      PMF.pure (prepareGuessInputFinish before beforeOutput 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true] 9) :=
  prepareGuessInput_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Padding in the frame counter is retained. With three unused blanks and
one counted bit, two original blanks survive beyond the two erased cells. -/
example : (skipFrameCellsPaddedFinish [some true] [some false] 1 [some true] 3).outputTape =
    { left := [some false], right := List.replicate 4 none } := rfl

example (savedInput savedOutput : List (Option Bool)) :
    evalConfigWithin preparePublicPrefixContext
      (preparePublicPrefixContextPaddedStart savedInput savedOutput 3 [false, true] [none, some false] 3)
      (preparePublicPrefixContextSteps 3 [false, true]) =
      PMF.pure (preparePublicPrefixContextFinish savedInput savedOutput 3 [false, true] [none, some false]) :=
  (preparePublicPrefixContextPadded_runs _ _ _ _ _ _ (by decide)).evalConfigWithin_eq_pure_of_no_randomBit
    preparePublicPrefixContext_no_randomBit

example : prepareGuessRequest.length = 183 := prepareGuessRequest_length
example : prepareGuessInput.length = 360 := prepareGuessInput_length

example (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product ≤
      250*(n + instanceBits.length + first.length + second.length + last.length + reply.length +
        message₀.length + message₁.length + state.length + selected.length + product.length + 1) + 800 :=
  prepareGuessInput_steps_le _ _ _ _ _ _ _ _ _ _ _

/-- Source randomness is supplied by the actual guarded source execution.
The saved caller bits are removed only by this mathematical observation;
this stage does not claim to have decoded or compared a source guess. -/
example (challenge : Bool) :
    (evalConfigWithin (GuardedCompiler.storedGuessCallCompile randomOutputBit)
      (GuardedCompiler.storedGuessCallStart [some challenge] [some false] [] 9)
      (GuardedCompiler.storedGuessCallTraceBudget (fun _ => 2) [])).map
        (fun c => (c.halted, c.inputTape.bits.drop 1)) =
      Foundation.Probability.sampleBit.map (fun bit => (true, [bit])) := by
  have h := GuardedCompiler.storedGuessCallCompile_evalRawReply randomOutputBit
    [some challenge] [some false] [] 9 (fun _ => 2) randomOutputBit_haltsWithin
  change (evalConfigWithin (GuardedCompiler.storedGuessCallCompile randomOutputBit)
      (GuardedCompiler.storedGuessCallStart [some challenge] [some false] [] 9)
      (GuardedCompiler.storedGuessCallTraceBudget (fun _ => 2) [])).map
        (fun c => (c.halted, c.inputTape.bits.drop 1)) =
      (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).map
        (fun c => (true, c.outputBits)) at h
  rw [h]
  have hSource := randomOutputBit_eval
  have hOutput := GuardedCompiler.preparedSource_evalOutput randomOutputBit [] 2
  have hHalts := GuardedCompiler.preparedSource_all_branches_halted randomOutputBit [] 2 randomOutputBit_haltsWithin
  have hBits : (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).map Configuration.outputBits =
      Foundation.Probability.sampleBit.map (fun bit => [bit]) := by
    have h := congrArg (fun law : PMF (Option (List Bool)) => law.map (fun out => out.getD []))
      (hOutput.trans hSource)
    simp only [PMF.map_comp, Function.comp_def] at h
    have heq : (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).map
        (fun c => (if c.halted then some c.outputBits else none).getD []) =
        (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).map Configuration.outputBits := by
      change (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).bind
        (fun c => PMF.pure ((if c.halted then some c.outputBits else none).getD [])) =
        (evalConfigWithin randomOutputBit (GuardedCompiler.preparedSource []) 2).bind
          (fun c => PMF.pure c.outputBits)
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext c hc
      exact congrArg (fun bit : Bool => PMF.pure ((if bit then some c.outputBits else none).getD []))
        (hHalts c ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc))
    rw [heq] at h
    simpa [PMF.map_comp, Function.comp_def] using h
  have h := congrArg (fun law : PMF (List Bool) => law.map (fun bits => (true, bits))) hBits
  simpa [PMF.map_comp, Function.comp_def] using h

/-- A fixed two-instruction randomized source is copied into a finite native
constructor. Its code length is independent of all security parameters and
all retained values. -/
example : (GuardedCompiler.guessFromProductCompile randomOutputBit).length = 661 := by
  rw [GuardedCompiler.guessFromProductCompile_length]
  rfl

/-- The complete request preparation and actual source invocation halt on
all source random branches. The premise is evaluated on this precise guess
request, including its state and ciphertext, rather than the DDH input size. -/
example (source : Program) (before beforeOutput : List (Option Bool)) (n padding : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (q : Nat → Nat)
    (halts : HaltsWithin source (GuardedCompiler.guessFromProductRequest n instanceBits second state product)
      (q (GuardedCompiler.guessFromProductRequest n instanceBits second state product).length)) :
    (evalConfigWithin (GuardedCompiler.guessFromProductCompile source)
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      (GuardedCompiler.guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product)).map Configuration.halted =
      PMF.pure true := by
  rw [GuardedCompiler.guessFromProductCompile_evalObservation source before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding q halts
    Configuration.halted (fun _ _ h => h.2.1)]
  change (evalConfigWithin source (GuardedCompiler.preparedSource (GuardedCompiler.guessFromProductRequest n instanceBits second state product))
    (q (GuardedCompiler.guessFromProductRequest n instanceBits second state product).length)).bind (fun _ => PMF.pure true) = _
  exact PMF.bind_const _ _

example (q : Nat → Nat) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    GuardedCompiler.guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product ≤
      3000*(n + instanceBits.length + first.length + second.length + last.length + reply.length +
        message₀.length + message₁.length + state.length + selected.length + product.length + 1)*
        (q (GuardedCompiler.guessFromProductRequest n instanceBits second state product).length + 1)^2 :=
  GuardedCompiler.guessFromProductBudget_bound _ _ _ _ _ _ _ _ _ _ _ _

end Machine.Examples
