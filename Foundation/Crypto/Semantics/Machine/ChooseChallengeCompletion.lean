import Foundation.Crypto.Semantics.Machine.ChooseInvocation
import Foundation.Crypto.Semantics.Machine.NormalizationGuessCompletion

namespace Machine.GuardedCompiler

/-- Fixed finite simulator pipeline: invoke the embedded choose code on the
actual encoded DDH input, then normalize its returned reply and run the
native challenge/multiply/guess continuation. None of the runtime payloads
or mathematical specifications below is inserted into this syntax. -/
def chooseChallengeGuessCompile (chooseSource normalizeSource multiplySource guessSource : Program) : Program :=
  let choose := chooseCompile chooseSource
  let pre := choose.asSubroutine 0 (choose.length + 1)
  let call := normalizationChallengeGuessCompile normalizeSource multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

theorem chooseChallengeGuessCompile_length (chooseSource normalizeSource multiplySource guessSource : Program) :
    (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource).length =
      68 * chooseSource.length + 68 * normalizeSource.length + 68 * multiplySource.length +
        68 * guessSource.length + 1764 := by
  simp only [chooseChallengeGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, chooseCompile_length, normalizationChallengeGuessCompile_length,
    List.length_cons, List.length_nil]
  omega

/-- The charged continuation budget for one actual returned source state.
The message/product functions are correctness specifications, not machine
primitives. Source scratch storage is retained and charged by this bound. -/
def chooseChallengeBranchBudget (qNormalize qMultiply qGuess : Nat → Nat)
    (chooseRequest : List Bool) (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) (c : Configuration) : Nat :=
  normalizationTraceBudget qNormalize n instanceBits
      (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) c.outputBits +
    (normalizationChallengeTailBudget qNormalize qMultiply qGuess chooseRequest n instanceBits
      first second last c.outputBits (message₀ c) (message₁ c) (state c) (product c) c + 1)

/-- A common finite upper bound over every source random branch. Finite
reachable-state enumeration is mathematical bookkeeping, not a simulator
instruction. This definition does not yet assert a polynomial majorant for
arbitrary supplied time functions. In particular, their monotonicity is
neither assumed nor used. -/
def chooseChallengeTailBudget (chooseSource : Program) (qChoose qNormalize qMultiply qGuess : Nat → Nat)
    (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) : Nat :=
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)
  ((reachableStates chooseSource (preparedSource request) (qChoose request.length)).map
    (chooseChallengeBranchBudget qNormalize qMultiply qGuess request n instanceBits
      first second last message₀ message₁ state product)).foldr max 0

private theorem le_foldr_max_of_mem (values : List Nat) (value : Nat) (h : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at h
  | cons head rest ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

theorem chooseChallengeTailBudget_fits
    (chooseSource : Program) (qChoose qNormalize qMultiply qGuess : Nat → Nat)
    (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) (c : Configuration)
    (hc : c ∈ (evalConfigWithin chooseSource
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)))
      (qChoose (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)).length)).support) :
    chooseChallengeBranchBudget qNormalize qMultiply qGuess
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)) n instanceBits
      first second last message₀ message₁ state product c ≤
        chooseChallengeTailBudget chooseSource qChoose qNormalize qMultiply qGuess n instanceBits
          first second last message₀ message₁ state product := by
  apply le_foldr_max_of_mem
  apply List.mem_map.mpr
  refine ⟨c, ?_, rfl⟩
  exact (mem_reachableStates_iff _ _ _ _).mpr ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)

/-- A uniform majorant for the individual charged continuations also bounds
the finite maximum, regardless of the number of random choose branches.
The enumeration itself is not charged as adversary execution. -/
theorem chooseChallengeTailBudget_le
    (chooseSource : Program) (qChoose qNormalize qMultiply qGuess : Nat → Nat)
    (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) (limit : Nat)
    (hLimit : ∀ c ∈ reachableStates chooseSource
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)))
      (qChoose (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)).length),
      chooseChallengeBranchBudget qNormalize qMultiply qGuess
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)) n instanceBits
        first second last message₀ message₁ state product c ≤ limit) :
    chooseChallengeTailBudget chooseSource qChoose qNormalize qMultiply qGuess n instanceBits
      first second last message₀ message₁ state product ≤ limit := by
  dsimp only [chooseChallengeTailBudget]
  generalize hValues : (List.map _ _) = values
  have hAll : ∀ value ∈ values, value ≤ limit := by
    intro value hValue
    rw [← hValues, List.mem_map] at hValue
    obtain ⟨c, hc, rfl⟩ := hValue
    exact hLimit c hc
  clear hValues
  induction values with
  | nil => exact Nat.zero_le _
  | cons head rest ih =>
      apply Nat.max_le.mpr
      exact ⟨hAll head (by simp), ih (by intro value h; exact hAll value (by simp [h]))⟩

/-- Source storage and raw output size are bounded on every prepared
choose branch by initial input storage plus its actual transition budget.
This does not select a successful branch or assume time monotonicity. -/
theorem preparedChooseBranch_size_le (source : Program) (request : List Bool) (steps : Nat)
    (c : Configuration) (hc : c ∈ reachableStates source (preparedSource request) steps) :
    sourceStorage c ≤ 2 * request.length + 2 + steps ∧
      c.outputBits.length ≤ 2 * request.length + 2 + steps := by
  have hRun := (mem_reachableStates_iff _ _ _ _).mp hc
  have hStorage := sourceStorage_le_of_padded_run hRun
  have hInitial := preparedSource_sourceStorage_le request
  have hBits := c.outputTape.bits_length_le_cells
  change c.outputBits.length ≤ c.outputTape.cells at hBits
  dsimp only [sourceStorage] at hStorage hInitial ⊢
  omega

/-- Ordinary execution of the complete pipeline from its initial finite
DDH input. The choose PMF feeds the normalizer and both native challenge
branches; the actual returned physical tapes are never reloaded for free.
All subsequent calls use their own input lengths in their time bounds. -/
theorem chooseChallengeGuessCompile_correct
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (qChoose qNormalize qMultiply qGuess : Nat → Nat) (n : Nat)
    (instanceBits first second last : List Bool)
    (nextBit tupleBit : Bool) (tail tupleRest : List Bool)
    (hRest : nextBit :: tail = FiniteBitEncoding.delimit second ++ last)
    (hTuple : tupleBit :: tupleRest = FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool)
    (hChoose : HaltsWithin chooseSource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first))
      (qChoose (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)).length))
    (hNormalize : ∀ input, HaltsWithin normalizeSource input (qNormalize input.length))
    (canonicalCorrect : ∀ c ∈ (evalConfigWithin chooseSource
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)))
        (qChoose (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)).length)).support,
      evalWithin normalizeSource (encodeSecurityParameter n ++ frame instanceBits ++ frame c.outputBits)
        (qNormalize (encodeSecurityParameter n ++ frame instanceBits ++ frame c.outputBits).length) =
          PMF.pure (some (canonicalMessageBits (message₀ c) (message₁ c) (state c))))
    (hMultiply : ∀ input, HaltsWithin multiplySource input (qMultiply input.length))
    (multiplyCorrect : ∀ c ∈ (evalConfigWithin chooseSource
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)))
        (qChoose (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)).length)).support,
      ∀ bit : Bool, evalWithin multiplySource
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ c else message₀ c) ++ frame last)
        (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++
          frame (if bit then message₁ c else message₀ c) ++ frame last).length) = PMF.pure (some (product c bit)))
    (hGuess : ∀ input, HaltsWithin guessSource input (qGuess input.length)) :
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)
    let tailBudget := chooseChallengeTailBudget chooseSource qChoose qNormalize qMultiply qGuess n instanceBits
      first second last message₀ message₁ state product
    (evalConfigWithin (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource)
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit first ++ nextBit :: tail)))
      (chooseTraceBudget qChoose n instanceBits first (nextBit :: tail) + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin chooseSource (preparedSource request) (qChoose request.length)).bind (fun c =>
        Foundation.Probability.sampleBit.bind (fun bit =>
          (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second (state c) (product c bit)))
            (qGuess (guessFromProductRequest n instanceBits second (state c) (product c bit)).length)).map
              (fun d => (true, [taggedGuessValue d.outputBits == bit])))) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: first)
  let original := encodeSecurityParameter n ++ frame instanceBits ++ frame (FiniteBitEncoding.delimit first ++ nextBit :: tail)
  let saved := none :: original.reverse.map some ++ [none]
  let choose := chooseCompile chooseSource
  let call := normalizationChallengeGuessCompile normalizeSource multiplySource guessSource
  let steps := chooseTraceBudget qChoose n instanceBits first (nextBit :: tail)
  let sourceDist := evalConfigWithin chooseSource (preparedSource request) (qChoose request.length)
  let stageDist := evalConfigWithin choose (Configuration.initial original) steps
  let tailBudget := chooseChallengeTailBudget chooseSource qChoose qNormalize qMultiply qGuess n instanceBits
    first second last message₀ message₁ state product
  let returned := fun c : Configuration =>
    { (rawResultFrom chooseSource request [none] saved c).swapTapes with
      pc := 119 + (rawCompileOpposite chooseSource).length + 1, halted := true }
  let observe := fun c : Configuration => (c.halted, c.outputBits)
  let continuation := fun c : Configuration => (evalConfigWithin call (c.resumeAt 0) tailBudget).map observe
  let expected := fun c : Configuration => Foundation.Probability.sampleBit.bind (fun bit =>
    (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second (state c) (product c bit)))
      (qGuess (guessFromProductRequest n instanceBits second (state c) (product c bit)).length)).map
        (fun d => (true, [taggedGuessValue d.outputBits == bit])))
  have hBody : FiniteBitEncoding.delimit first ++ nextBit :: tail = tupleBit :: tupleRest := by
    rw [hRest, hTuple]
    exact (List.append_assoc _ _ _).symm
  have hRaw (c : Configuration) (hc : c ∈ sourceDist.support) : continuation (returned c) = expected c := by
    let blanks := 2 * c.outputTape.cells + 2 - c.outputBits.length
    have hEntry := rawResultFrom_normalizationStart chooseSource request n instanceBits tupleBit tupleRest c
    dsimp only at hEntry
    have hStart : (returned c).resumeAt 0 =
        prepareChooseNormalizationStart ((rawResultFrom chooseSource request [none] saved c).swapTapes).outputTape.left
          n instanceBits tupleBit tupleRest c.outputBits blanks := by
      simpa only [returned, saved, original, hBody, Configuration.resumeAt] using hEntry
    have hNative := normalizationChallengeGuessCompile_correct chooseSource normalizeSource multiplySource guessSource
      qNormalize qMultiply qGuess request saved n instanceBits first second last c.outputBits
      (message₀ c) (message₁ c) (state c) tupleBit tupleRest hTuple (product c) c blanks
      (hNormalize _) (canonicalCorrect c hc) (fun _ => hMultiply _) (multiplyCorrect c hc) (fun _ => hGuess _)
    dsimp only at hNative
    have hLaw : (evalConfigWithin call ((returned c).resumeAt 0)
        (chooseChallengeBranchBudget qNormalize qMultiply qGuess request n instanceBits
          first second last message₀ message₁ state product c)).map observe = expected c := by
      simpa only [call, chooseChallengeBranchBudget, hStart, hTuple, expected, observe] using hNative
    have hHalts : ∀ d, PaddedRunsFor call ((returned c).resumeAt 0) d
        (chooseChallengeBranchBudget qNormalize qMultiply qGuess request n instanceBits
          first second last message₀ message₁ state product c) → d.halted = true := by
      intro d run
      have hm := (PMF.mem_support_map_iff observe _ (observe d)).mpr
        ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
      rw [hLaw, PMF.mem_support_bind_iff] at hm
      obtain ⟨bit, _hb, hm⟩ := hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨e, _he, heq⟩ := hm
      exact (congrArg Prod.fst heq).symm
    dsimp only [continuation]
    rw [evalConfigWithin_eq_of_le call _ _ tailBudget
      (chooseChallengeTailBudget_fits chooseSource qChoose qNormalize qMultiply qGuess n instanceBits
        first second last message₀ message₁ state product c hc) hHalts]
    exact hLaw
  have hFuture := chooseCompile_evalObservation chooseSource n instanceBits first nextBit tail qChoose hChoose
    continuation (by
      intro c d h
      apply evalConfigWithin_map_eq_of_equivalent
      · exact (h.withPc 0).withHalted false
      · intro c d h; exact congrArg₂ Prod.mk h.2.1 h.outputBits)
  have hBind := congrArg (fun distribution : PMF (PMF (Bool × List Bool)) => distribution.bind id) hFuture
  simp only [PMF.bind_map, Function.comp_def, id_eq] at hBind
  have hContinuation : stageDist.bind continuation = sourceDist.bind expected := by
    change stageDist.bind continuation = _ at hBind
    rw [hBind]
    change sourceDist.bind _ = _
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext c hc
    exact hRaw c hc
  have hSecond : ∀ c ∈ stageDist.support,
      ∀ d, PaddedRunsFor call (c.resumeAt 0) d tailBudget → d.halted = true := by
    intro c hc d run
    have hm : observe d ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_bind_iff] at hm
    obtain ⟨sourceResult, _hSource, hm⟩ := hm
    rw [PMF.mem_support_bind_iff] at hm
    obtain ⟨bit, _hb, hm⟩ := hm
    rw [PMF.mem_support_map_iff] at hm
    obtain ⟨e, _he, heq⟩ := hm
    exact (congrArg Prod.fst heq).symm
  have h := Program.evalConfigWithin_twoStages choose call (Configuration.initial original) rfl rfl steps tailBudget
    (chooseCompile_haltsWithin chooseSource n instanceBits first nextBit tail qChoose hChoose) hSecond
  exact h.trans hContinuation

end Machine.GuardedCompiler
