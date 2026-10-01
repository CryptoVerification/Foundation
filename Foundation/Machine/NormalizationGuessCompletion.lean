import Foundation.Machine.NormalizedGuessCompletion

namespace Machine.GuardedCompiler

/-- Run the actual normalization source, then the complete native fair-bit,
message-selection, multiplication and guess continuation on its returned
tapes. All three supplied programs are fixed finite code. -/
def normalizationChallengeGuessCompile (normalizeSource multiplySource guessSource : Program) : Program :=
  let normalize := normalizeChooseCompile normalizeSource
  let pre := normalize.asSubroutine 0 (normalize.length + 1)
  let call := normalizedMultiplyGuessCompile multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

theorem normalizationChallengeGuessCompile_length (normalizeSource multiplySource guessSource : Program) :
    (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource).length =
      68 * normalizeSource.length + 68 * multiplySource.length + 68 * guessSource.length + 1485 := by
  simp only [normalizationChallengeGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, normalizeChooseCompile_length, normalizedMultiplyGuessCompile_length,
    List.length_cons, List.length_nil]
  omega

/-- The outer frame of the nonempty three-element tuple already stored in
the caller cells. This identity joins layouts; it is not a machine opcode. -/
theorem multiplyTupleTail_frame (first second last : List Bool) :
    true :: multiplyTupleTail first second last =
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) := by
  let tuple := FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last
  have hLength : tuple.length - 1 + 1 = tuple.length := by
    simp only [tuple, List.length_append, FiniteBitEncoding.delimit_length]
    omega
  have hRep : List.replicate tuple.length true = true :: List.replicate (tuple.length - 1) true := by
    calc
      _ = List.replicate (tuple.length - 1 + 1) true := congrArg (fun m => List.replicate m true) hLength.symm
      _ = _ := List.replicate_succ
  change true :: (List.replicate (tuple.length - 1) true ++ false :: tuple) = frame tuple
  simp only [frame, hRep, List.cons_append, List.append_assoc, List.nil_append]

private theorem normalizer_output_eq (source : Program) (request canonical : List Bool) (steps : Nat)
    (halts : HaltsWithin source request steps)
    (correct : evalWithin source request steps = PMF.pure (some canonical))
    (c : Configuration) (hc : c ∈ (evalConfigWithin source (preparedSource request) steps).support) :
    c.outputBits = canonical := by
  have hHalted := preparedSource_all_branches_halted source request steps halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hMem := (PMF.mem_support_map_iff
    (fun d : Configuration => if d.halted then some d.outputBits else none) _
    (if c.halted then some c.outputBits else none)).mpr ⟨c, hc, rfl⟩
  rw [preparedSource_evalOutput, correct, PMF.mem_support_pure_iff] at hMem
  simpa only [hHalted, ↓reduceIte, Option.some.injEq] using hMem

/-- Ordinary execution from the retained choose return. Every normalization
scratch branch feeds the same native continuation, at one common bound.
Canonical correctness fixes the interpreted messages, while the actual
normalizer/source configurations remain on the tapes until charged cleanup. -/
theorem normalizationChallengeGuessCompile_evalResult
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (qNormalize qMultiply qGuess : Nat → Nat) (chooseRequest : List Bool)
    (chooseSaved : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (tupleBit : Bool) (tupleRest : List Bool)
    (hTuple : tupleBit :: tupleRest = FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    (product : Bool → List Bool) (chooseResult : Configuration) (blanks tailBudget : Nat)
    (hNormalize : HaltsWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (canonicalCorrect : evalWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length) =
        PMF.pure (some (canonicalMessageBits message₀ message₁ state)))
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (multiplyCorrect : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length))
    (hFits : ∀ c ∈ (evalConfigWithin normalizeSource
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
        (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).support,
      prepareSelectedMessageSteps message₀ message₁ state +
        (normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest
          (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) n instanceBits
          first second last reply message₀ message₁ state product chooseResult c + 1) ≤ tailBudget) :
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    (evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
      (prepareChooseNormalizationStart chooseReturn.outputTape.left n instanceBits tupleBit tupleRest reply blanks)
      (normalizationTraceBudget qNormalize n instanceBits (tupleBit :: tupleRest) reply + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
          (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let original := encodeSecurityParameter n ++ frame instanceBits ++ frame (tupleBit :: tupleRest)
  let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
  let saved := none :: (reply.reverse.map some ++ none :: original.reverse.map some ++ [none])
  let start := prepareChooseNormalizationStart chooseReturn.outputTape.left n instanceBits tupleBit tupleRest reply blanks
  let normalize := normalizeChooseCompile normalizeSource
  let call := normalizedMultiplyGuessCompile multiplySource guessSource
  let steps := normalizationTraceBudget qNormalize n instanceBits (tupleBit :: tupleRest) reply
  let sourceDist := evalConfigWithin normalizeSource (preparedSource request) (qNormalize request.length)
  let stageDist := evalConfigWithin normalize start steps
  let returned := fun c : Configuration =>
    { (rawResultFrom normalizeSource request (none :: chooseReturn.outputTape.left) saved c).swapTapes with
      pc := 95 + (rawCompileOpposite normalizeSource).length + 1, halted := true }
  let observe := fun c : Configuration => (c.halted, c.outputBits)
  let continuation := fun c : Configuration => (evalConfigWithin call (c.resumeAt 0) tailBudget).map observe
  let expected := Foundation.Probability.sampleBit.bind (fun bit =>
    (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
        (fun c => (true, [taggedGuessValue c.outputBits == bit])))
  have hOriginal : original = encodeSecurityParameter n ++ frame instanceBits ++
      true :: multiplyTupleTail first second last := by
    dsimp only [original]
    rw [hTuple, multiplyTupleTail_frame]
  have hRaw (c : Configuration) (hc : c ∈ sourceDist.support) : continuation (returned c) = expected := by
    have hOutput := normalizer_output_eq normalizeSource request (canonicalMessageBits message₀ message₁ state)
      (qNormalize request.length) hNormalize canonicalCorrect c hc
    have hNative := normalizedMultiplyGuessCompile_fromNormalizer_correct chooseSource normalizeSource multiplySource guessSource
      qMultiply qGuess chooseRequest request chooseSaved [] n instanceBits first second last reply message₀ message₁ state
      product chooseResult c hOutput hMultiply multiplyCorrect hGuess
    dsimp only at hNative
    have hNativeHalts : ∀ d, PaddedRunsFor call ((returned c).resumeAt 0) d
        (prepareSelectedMessageSteps message₀ message₁ state +
          (normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest request n instanceBits
            first second last reply message₀ message₁ state product chooseResult c + 1)) → d.halted = true := by
      intro d run
      have hd := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
      have hm := (PMF.mem_support_map_iff observe _ (observe d)).mpr ⟨d, hd, rfl⟩
      have hLaw : (evalConfigWithin call ((returned c).resumeAt 0)
          (prepareSelectedMessageSteps message₀ message₁ state +
            (normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest request n instanceBits
              first second last reply message₀ message₁ state product chooseResult c + 1))).map observe = expected := by
        simpa only [call, returned, saved, hOriginal, List.append_nil, Configuration.resumeAt] using hNative
      rw [hLaw, PMF.mem_support_bind_iff] at hm
      obtain ⟨bit, _hb, hm⟩ := hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨e, _he, heq⟩ := hm
      exact (congrArg Prod.fst heq).symm
    dsimp only [continuation]
    rw [evalConfigWithin_eq_of_le call _ _ tailBudget (hFits c hc) hNativeHalts]
    simpa only [call, returned, saved, hOriginal, List.append_nil, Configuration.resumeAt] using hNative
  have hObserve : ∀ c d, c.Equivalent d → continuation c = continuation d := by
    intro c d h
    apply evalConfigWithin_map_eq_of_equivalent
    · exact (h.withPc 0).withHalted false
    · intro c d h; exact congrArg₂ Prod.mk h.2.1 h.outputBits
  have hFuture := normalizeChooseCompile_evalObservation normalizeSource chooseReturn.outputTape.left n instanceBits
    tupleBit tupleRest reply blanks qNormalize hNormalize continuation hObserve
  have hBind := congrArg (fun distribution : PMF (PMF (Bool × List Bool)) => distribution.bind id) hFuture
  simp only [PMF.bind_map, Function.comp_def, id_eq] at hBind
  have hContinuation : stageDist.bind continuation = expected := by
    change stageDist.bind continuation = _ at hBind
    rw [hBind]
    change sourceDist.bind _ = _
    rw [← PMF.bindOnSupport_eq_bind]
    calc
      _ = sourceDist.bindOnSupport (fun _ _ => expected) := by
        congr 1
        funext c hc
        simpa only [returned, saved, request, original, List.append_assoc, List.cons_append] using hRaw c hc
      _ = expected := by rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]
  have hSecond : ∀ c ∈ stageDist.support,
      ∀ d, PaddedRunsFor call (c.resumeAt 0) d tailBudget → d.halted = true := by
    intro c hc d run
    have hm : observe d ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_bind_iff] at hm
    obtain ⟨bit, _hb, hm⟩ := hm
    rw [PMF.mem_support_map_iff] at hm
    obtain ⟨e, _he, heq⟩ := hm
    exact (congrArg Prod.fst heq).symm
  have h := Program.evalConfigWithin_twoStages normalize call start rfl rfl steps tailBudget
    (normalizeChooseCompile_haltsFrom normalizeSource chooseReturn.outputTape.left n instanceBits tupleBit tupleRest
      reply blanks qNormalize hNormalize) hSecond
  exact h.trans hContinuation

/-- An explicit common continuation budget for all actual normalizer
scratch branches. Each source transition can enlarge stored tapes by at
most one cell; the prepared input's storage supplies the finite initial
allowance. This budget never assumes source time functions are monotone. -/
def normalizationChallengeTailBudget (qNormalize qMultiply qGuess : Nat → Nat)
    (chooseRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult : Configuration) : Nat :=
  let normalizeRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let selected := fun bit : Bool => if bit then message₁ else message₀
  let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
  let guessRequest := fun bit => guessFromProductRequest n instanceBits second state (product bit)
  let allowance := 2 * normalizeRequest.length + 2 + qNormalize normalizeRequest.length
  let size := fun bit => n + instanceBits.length + first.length + second.length + last.length + reply.length +
    message₀.length + message₁.length + state.length + (selected bit).length + (product bit).length +
    (multiplyRequest bit).length + (guessRequest bit).length + chooseRequest.length + normalizeRequest.length +
    sourceStorage chooseResult + allowance + 1
  let time := qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  prepareSelectedMessageSteps message₀ message₁ state + (20000 * (size false + size true) * time^2 + 1)

theorem normalizationChallengeTailBudget_fits
    (normalizeSource : Program) (qNormalize qMultiply qGuess : Nat → Nat)
    (chooseRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult c : Configuration)
    (hc : c ∈ (evalConfigWithin normalizeSource
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).support) :
    prepareSelectedMessageSteps message₀ message₁ state +
      (normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest
        (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) n instanceBits
        first second last reply message₀ message₁ state product chooseResult c + 1) ≤
    normalizationChallengeTailBudget qNormalize qMultiply qGuess chooseRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult := by
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  have hStorage := sourceStorage_le_of_padded_run ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  change sourceStorage c ≤ sourceStorage (preparedSource request) + qNormalize request.length at hStorage
  have hInitial := preparedSource_sourceStorage_le request
  have hAllowance : sourceStorage c ≤ 2 * request.length + 2 + qNormalize request.length := by omega
  have h := normalizedMultiplyGuessTailBudget_bound qMultiply qGuess chooseRequest request n instanceBits
    first second last reply message₀ message₁ state product chooseResult c
  dsimp only at h
  dsimp only [request] at hAllowance h
  dsimp only [normalizationChallengeTailBudget]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_right
  apply h.trans
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  omega

/-- Canonical correctness and the explicit storage/step majorant discharge
all normalizer-branch continuation bounds. The same native code performs
normalization and the full randomized challenge/guess continuation. -/
theorem normalizationChallengeGuessCompile_correct
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (qNormalize qMultiply qGuess : Nat → Nat) (chooseRequest : List Bool)
    (chooseSaved : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (tupleBit : Bool) (tupleRest : List Bool)
    (hTuple : tupleBit :: tupleRest = FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    (product : Bool → List Bool) (chooseResult : Configuration) (blanks : Nat)
    (hNormalize : HaltsWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (canonicalCorrect : evalWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length) =
        PMF.pure (some (canonicalMessageBits message₀ message₁ state)))
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (multiplyCorrect : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)) :
    let tailBudget := normalizationChallengeTailBudget qNormalize qMultiply qGuess chooseRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    (evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
      (prepareChooseNormalizationStart chooseReturn.outputTape.left n instanceBits tupleBit tupleRest reply blanks)
      (normalizationTraceBudget qNormalize n instanceBits (tupleBit :: tupleRest) reply + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
          (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  exact normalizationChallengeGuessCompile_evalResult chooseSource normalizeSource multiplySource guessSource
    qNormalize qMultiply qGuess chooseRequest chooseSaved n instanceBits first second last reply message₀ message₁ state
    tupleBit tupleRest hTuple product chooseResult blanks
    (normalizationChallengeTailBudget qNormalize qMultiply qGuess chooseRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult)
    hNormalize canonicalCorrect hMultiply multiplyCorrect hGuess (by
      intro c hc
      exact normalizationChallengeTailBudget_fits normalizeSource qNormalize qMultiply qGuess chooseRequest n instanceBits
        first second last reply message₀ message₁ state product chooseResult c hc)

/-- Every random normalization, challenge and guess branch of this same
code halts at the explicit common step bound. -/
theorem normalizationChallengeGuessCompile_correct_haltsFrom
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (qNormalize qMultiply qGuess : Nat → Nat) (chooseRequest : List Bool)
    (chooseSaved : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (tupleBit : Bool) (tupleRest : List Bool)
    (hTuple : tupleBit :: tupleRest = FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    (product : Bool → List Bool) (chooseResult : Configuration) (blanks : Nat)
    (hNormalize : HaltsWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (canonicalCorrect : evalWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length) =
        PMF.pure (some (canonicalMessageBits message₀ message₁ state)))
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (multiplyCorrect : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)) :
    let tailBudget := normalizationChallengeTailBudget qNormalize qMultiply qGuess chooseRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    ∀ c, PaddedRunsFor (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
      (prepareChooseNormalizationStart chooseReturn.outputTape.left n instanceBits tupleBit tupleRest reply blanks) c
      (normalizationTraceBudget qNormalize n instanceBits (tupleBit :: tupleRest) reply + (tailBudget + 1)) → c.halted = true := by
  dsimp only
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, hc, rfl⟩
  rw [normalizationChallengeGuessCompile_correct chooseSource normalizeSource multiplySource guessSource
    qNormalize qMultiply qGuess chooseRequest chooseSaved n instanceBits first second last reply message₀ message₁ state
    tupleBit tupleRest hTuple product chooseResult blanks hNormalize canonicalCorrect hMultiply multiplyCorrect hGuess,
    PMF.mem_support_bind_iff] at hm
  obtain ⟨bit, _hb, hm⟩ := hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨d, _hd, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm


/-- A common polynomial envelope covers the actual normalizer request,
its returned guarded scratch, and the full selection/multiply/guess tail.
All bitstring inputs and normalizer responses are permitted. -/
def normalizationChallengeRetainedBudget
    (normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage : Nat) : Nat :=
  let requestLimit := 200000001 * (storage + 1)
  let normalizationTime := normalizationCoefficient * (requestLimit + 1)^normalizationDegree
  let retainedSize := 100 * (requestLimit + normalizationTime + 1)
  normalizationRetainedBudget normalizationCoefficient normalizationDegree storage +
    normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree retainedSize + 1

theorem normalizationChallengeRetainedBudget_polynomial_of_profile
    (normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n => normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree (size n)) := by
  have hLimit := (PolynomiallyBounded.const 200000001).mul (hSize.add (PolynomiallyBounded.const 1))
  have hTime := (PolynomiallyBounded.const normalizationCoefficient).mul
    ((hLimit.add (PolynomiallyBounded.const 1)).pow normalizationDegree)
  have hRetained := (PolynomiallyBounded.const 100).mul
    ((hLimit.add hTime).add (PolynomiallyBounded.const 1))
  have hFirst := normalizationRetainedBudget_polynomial_of_profile normalizationCoefficient normalizationDegree hSize
  have hTail := normalizedMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hRetained
  exact (hFirst.add hTail).add (PolynomiallyBounded.const 1)

theorem normalizationChallengeRetainedBudget_polynomial
    (normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    PolynomiallyBounded (normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree) :=
  normalizationChallengeRetainedBudget_polynomial_of_profile normalizationCoefficient normalizationDegree
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree PolynomiallyBounded.id

theorem normalizationChallengeRetainedBudget_monotone
    (normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    Monotone (normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree) := by
  intro a b h
  have hLimit := Nat.mul_le_mul_left 200000001 (Nat.add_le_add_right h 1)
  have hTime := Nat.mul_le_mul_left normalizationCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hLimit 1) normalizationDegree)
  have hRetained := Nat.mul_le_mul_left 100 (Nat.add_le_add_right (Nat.add_le_add hLimit hTime) 1)
  have hFirst := normalizationRetainedBudget_monotone normalizationCoefficient normalizationDegree h
  have hTail := normalizedMultiplyGuessRetainedBudget_monotone multiplyCoefficient multiplyDegree guessCoefficient guessDegree hRetained
  exact Nat.add_le_add_right (Nat.add_le_add hFirst hTail) 1

/-- Native normalization and the entire native challenge/multiply/guess
continuation stop on every branch of every finite retained choose reply.
Malformed public data and arbitrary normalizer output bits are included.
Each stage executes on its actual returned physical tapes; no decoder,
canonical normalizer correctness or group-operation correctness is used. -/
theorem normalizationChallengeGuessCompile_haltsFrom_retainedReply
    (normalizeSource multiplySource guessSource : Program)
    (normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hNormalizer : ∀ request : List Bool,
      HaltsWithin normalizeSource request (normalizationCoefficient * (request.length + 1)^normalizationDegree))
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (beforeInput savedOutput : List (Option Bool)) (reply : List Bool) (inputBlanks outputBlanks : Nat) :
    let start : Configuration := {
      inputTape := {
        left := reply.reverse.map some ++ none :: beforeInput
        right := List.replicate inputBlanks none },
      outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    ∀ finish, PaddedRunsFor (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource) start finish
      (normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
        multiplyCoefficient multiplyDegree guessCoefficient guessDegree (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let start : Configuration := {
    inputTape := {
      left := reply.reverse.map some ++ none :: beforeInput
      right := List.replicate inputBlanks none },
    outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let storage := sourceStorage start
  let q := fun m => normalizationCoefficient * (m + 1)^normalizationDegree
  let requestLimit := 200000001 * (storage + 1)
  let normalizationTime := normalizationCoefficient * (requestLimit + 1)^normalizationDegree
  let retainedSize := 100 * (requestLimit + normalizationTime + 1)
  let firstTime := normalizationRetainedBudget normalizationCoefficient normalizationDegree storage
  let tailTime := normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree retainedSize
  let stageDist := evalConfigWithin (normalizeChooseCompile normalizeSource) start firstTime
  let continuation : Configuration → PMF Bool := fun c =>
    (evalConfigWithin (normalizedMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) tailTime).map Configuration.halted
  have hObserve (c d : Configuration) (h : c.Equivalent d) : continuation c = continuation d := by
    apply evalConfigWithin_map_eq_of_equivalent
      (normalizedMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) (d.resumeAt 0) _ tailTime
      Configuration.halted (fun _ _ h => h.2.1)
    exact (h.withPc 0).withHalted false
  obtain ⟨request, sourceSaved, targetSaved, hLength, hPrefix, hFuture⟩ :=
    normalizeChooseCompile_evalObservation_from_retainedReply normalizeSource normalizationCoefficient normalizationDegree
      hNormalizer beforeInput savedOutput reply inputBlanks outputBlanks continuation hObserve
  let returned := fun c => {
    (rawResultFrom normalizeSource request sourceSaved targetSaved c).swapTapes
    with pc := 95 + (rawCompileOpposite normalizeSource).length + 1, halted := true }
  let sourceDist := evalConfigWithin normalizeSource (preparedSource request) (q request.length)
  have hRequest : request.length ≤ requestLimit := hLength
  have hSourceTime : q request.length ≤ normalizationTime :=
    Nat.mul_le_mul_left normalizationCoefficient
      (Nat.pow_le_pow_left (Nat.add_le_add_right hRequest 1) normalizationDegree)
  have hRaw (c : Configuration) (hc : c ∈ sourceDist.support) : continuation (returned c) = PMF.pure true := by
    have hSourceStorage := sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    have hInitial := preparedSource_sourceStorage_le request
    have hReturned := rawResultFrom_sourceStorage_le normalizeSource request sourceSaved targetSaved c
    have hStorage : sourceStorage (returned c) ≤ retainedSize := by
      change sourceStorage c ≤ sourceStorage (preparedSource request) + q request.length at hSourceStorage
      change sourceSaved.length + targetSaved.length ≤ requestLimit at hPrefix
      have hReturnStorage : sourceStorage (returned c) =
          sourceStorage (rawResultFrom normalizeSource request sourceSaved targetSaved c) := by
        simp only [returned, sourceStorage, Configuration.swapTapes, Nat.add_comm]
      rw [hReturnStorage]
      change _ ≤ 100 * (requestLimit + normalizationTime + 1)
      omega
    have hSmall := normalizedMultiplyGuessCompile_fromRawResult_haltsFrom_raw
      normalizeSource multiplySource guessSource multiplyCoefficient multiplyDegree guessCoefficient guessDegree
      hMultiply hGuess request sourceSaved targetSaved c
    change ∀ d, PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) ((returned c).resumeAt 0) d
      (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage (returned c))) → d.halted = true at hSmall
    have hBudget := normalizedMultiplyGuessRetainedBudget_monotone
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree hStorage
    have hStop (d : Configuration)
        (run : PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) ((returned c).resumeAt 0) d tailTime) :
        d.halted = true := by
      have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
      rw [evalConfigWithin_eq_of_le _ _ _ _ hBudget hSmall] at hMem
      exact hSmall d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
    dsimp only [continuation]
    calc
      _ = (evalConfigWithin (normalizedMultiplyGuessCompile multiplySource guessSource)
          ((returned c).resumeAt 0) tailTime).bind (fun _ => PMF.pure true) := by
        rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
        congr 1
        funext d hd
        change PMF.pure d.halted = PMF.pure true
        rw [hStop d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hd)]
      _ = _ := PMF.bind_const _ _
  have hBind := congrArg (fun distribution : PMF (PMF Bool) => distribution.bind id) hFuture
  simp only [PMF.bind_map, Function.comp_def, id_eq] at hBind
  have hContinuation : stageDist.bind continuation = PMF.pure true := by
    change stageDist.bind continuation = sourceDist.bind (fun c => continuation (returned c)) at hBind
    rw [hBind]
    rw [← PMF.bind_const sourceDist (PMF.pure true)]
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext c hc
    exact hRaw c hc
  have hFirst := normalizeChooseCompile_haltsFrom_retainedReply normalizeSource normalizationCoefficient normalizationDegree
    hNormalizer beforeInput savedOutput reply inputBlanks outputBlanks
  have hSecond (c : Configuration) (hc : c ∈ stageDist.support) (d : Configuration)
      (run : PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) d tailTime) :
      d.halted = true := by
    have hm : d.halted ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_pure_iff] at hm
    exact hm
  have hLaw := Program.evalConfigWithin_twoStages_configuration (normalizeChooseCompile normalizeSource)
    (normalizedMultiplyGuessCompile multiplySource guessSource) start rfl rfl firstTime tailTime hFirst hSecond
  change evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource) start
    (firstTime + (tailTime + 1)) = _ at hLaw
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  change finish ∈ (evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource) start
    (firstTime + tailTime + 1)).support at hMem
  rw [Nat.add_assoc, hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
  rw [PMF.mem_support_map_iff] at hFinish
  obtain ⟨target, _hTarget, rfl⟩ := hFinish
  rfl

end Machine.GuardedCompiler
