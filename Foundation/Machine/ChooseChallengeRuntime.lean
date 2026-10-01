import Foundation.Machine.ChooseChallengeCompletion

namespace Machine.GuardedCompiler

/-- A numerical majorant for one complete continuation. Payload sizes and
source storage are charged explicitly; every time function is evaluated at
the actual request length of its own invocation. This bound does not assume
that those functions are monotone. It will support a common polynomial
envelope over choose branches once their sizes and times are bounded. -/
theorem chooseChallengeBranchBudget_bound
    (qNormalize qMultiply qGuess : Nat → Nat) (chooseRequest : List Bool)
    (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) (c : Configuration) :
    let reply := c.outputBits
    let normalRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let selected := fun bit : Bool => if bit then message₁ c else message₀ c
    let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
    let guessRequest := fun bit => guessFromProductRequest n instanceBits second (state c) (product c bit)
    let size := n + instanceBits.length + first.length + second.length + last.length +
      chooseRequest.length + reply.length + (message₀ c).length + (message₁ c).length + (state c).length +
      (product c false).length + (product c true).length + sourceStorage c + 1
    let normalizeTime := qNormalize normalRequest.length
    let time := normalizeTime + qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
      qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
    chooseChallengeBranchBudget qNormalize qMultiply qGuess chooseRequest n instanceBits first second last
      message₀ message₁ state product c ≤ 1300000 * (size + normalizeTime) * time^2 := by
  dsimp only
  let reply := c.outputBits
  let normalRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let selected := fun bit : Bool => if bit then message₁ c else message₀ c
  let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
  let guessRequest := fun bit => guessFromProductRequest n instanceBits second (state c) (product c bit)
  let size := n + instanceBits.length + first.length + second.length + last.length +
    chooseRequest.length + reply.length + (message₀ c).length + (message₁ c).length + (state c).length +
    (product c false).length + (product c true).length + sourceStorage c + 1
  let normalizeTime := qNormalize normalRequest.length
  let weight := size + normalizeTime
  let tailTime := qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  let time := normalizeTime + qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  let branchSize := fun bit => n + instanceBits.length + first.length + second.length + last.length + reply.length +
    (message₀ c).length + (message₁ c).length + (state c).length + (selected bit).length + (product c bit).length +
    (multiplyRequest bit).length + (guessRequest bit).length + chooseRequest.length + normalRequest.length +
    sourceStorage c + (2 * normalRequest.length + 2 + normalizeTime) + 1
  have hPositive : 1 ≤ size := by dsimp only [size]; omega
  have hWeight : size ≤ weight := Nat.le_add_right _ _
  have hTime : 1 ≤ time := by dsimp only [time]; omega
  have hNormTime : normalizeTime + 1 ≤ time := by dsimp only [time]; omega
  have hTailTime : tailTime ≤ time := by dsimp only [tailTime, time]; omega
  have hSquare : 1 ≤ time ^ 2 := Nat.one_le_pow _ _ hTime
  have hMultiplyLen (bit : Bool) : (multiplyRequest bit).length ≤ 5 * size := by
    cases bit <;> simp only [multiplyRequest, selected, Bool.false_eq_true, ↓reduceIte,
      encodeSecurityParameter, frame, List.length_append, List.length_cons, List.length_replicate] <;>
      simp only [List.length_nil] <;>
      dsimp only [size] <;> omega
  have hGuessLen (bit : Bool) : (guessRequest bit).length ≤ 10 * size := by
    cases bit <;> simp only [guessRequest, guessFromProductRequest, encodeSecurityParameter, frame,
      List.length_append, List.length_cons, List.length_replicate, FiniteBitEncoding.delimit_length] <;>
      simp only [List.length_nil] <;>
      dsimp only [size] <;> omega
  have hNormalLen : normalRequest.length ≤ 3 * size := by
    simp only [normalRequest, encodeSecurityParameter, frame, List.length_append,
      List.length_cons, List.length_replicate, List.length_nil]
    dsimp only [size]
    omega
  have hBranchSize (bit : Bool) : branchSize bit ≤ 30 * weight := by
    have hm := hMultiplyLen bit
    have hg := hGuessLen bit
    cases bit <;> dsimp only [branchSize, selected, weight, size] at * <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hPrepare := prepareSelectedMessage_steps_le (message₀ c) (message₁ c) (state c)
  have hPrepareBound : prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) ≤ 150 * size := by
    simp only [canonicalMessageBits, List.length_cons, List.length_append, FiniteBitEncoding.delimit_length] at hPrepare
    dsimp only [size]
    omega
  have hOriginal : (encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)).length + reply.length + 1 ≤ 8 * size := by
    simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hNorm := normalizationTraceBudget_bound qNormalize n instanceBits
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply
  have hNormBound : normalizationTraceBudget qNormalize n instanceBits
      (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply ≤
        2800 * weight * time ^ 2 := by
    apply hNorm.trans
    change 350 * _ * (normalizeTime + 1)^2 ≤ _
    calc
      _ ≤ 350 * (8 * size) * time^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 350 hOriginal) (Nat.pow_le_pow_left hNormTime 2)
      _ ≤ 350 * (8 * weight) * time^2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 350 (Nat.mul_le_mul_left 8 hWeight))
      _ = _ := by simp only [← Nat.mul_assoc, Nat.reduceMul]
  have hTailBound : 20000 * (branchSize false + branchSize true) * tailTime^2 ≤
      1200000 * weight * time^2 := by
    calc
      _ ≤ 20000 * (60 * weight) * time^2 := by
        have hSize : branchSize false + branchSize true ≤ 60 * weight := by
          simpa only [← Nat.add_mul, Nat.reduceAdd] using
            Nat.add_le_add (hBranchSize false) (hBranchSize true)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 20000 hSize) (Nat.pow_le_pow_left hTailTime 2)
      _ = _ := by simp only [← Nat.mul_assoc, Nat.reduceMul]
  have hPrepareScaled : prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) ≤
      150 * weight * time^2 := by
    calc
      _ ≤ 150 * size := hPrepareBound
      _ ≤ 150 * weight := Nat.mul_le_mul_left 150 hWeight
      _ = 150 * weight * 1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hSquare
  have hUnit : 1 ≤ weight * time^2 := by
    have hWeightPositive : 1 ≤ weight := hPositive.trans hWeight
    simpa only [Nat.one_mul] using Nat.mul_le_mul hWeightPositive hSquare
  change normalizationTraceBudget qNormalize n instanceBits
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply +
      (prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) +
        (20000 * (branchSize false + branchSize true) * tailTime^2 + 1) + 1) ≤ 1300000 * weight * time^2
  simp only [Nat.mul_assoc] at hNormBound hTailBound hPrepareScaled ⊢
  omega


/-- One input-length polynomial envelope for the whole native simulator.
Every source is evaluated at its actual request length. Saved caller and
source scratch cells are retained, with their physical sizes charged. -/
def chooseChallengeAllInputBudget
    (chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) (m : Nat) : Nat :=
  let requestLimit := 20000003 * (m + 1)
  let chooseTime := chooseCoefficient * (requestLimit + 1)^chooseDegree
  let retainedSize := 100 * (requestLimit + chooseTime + 1)
  chooseAllInputBudget chooseCoefficient chooseDegree m +
    normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree retainedSize + 1

theorem chooseChallengeAllInputBudget_polynomial
    (chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    PolynomiallyBounded (chooseChallengeAllInputBudget chooseCoefficient chooseDegree
      normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree) := by
  have hLimit := (PolynomiallyBounded.const 20000003).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
  have hTime := (PolynomiallyBounded.const chooseCoefficient).mul
    ((hLimit.add (PolynomiallyBounded.const 1)).pow chooseDegree)
  have hSize := (PolynomiallyBounded.const 100).mul
    ((hLimit.add hTime).add (PolynomiallyBounded.const 1))
  have hTail := normalizationChallengeRetainedBudget_polynomial_of_profile
    normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree hSize
  exact ((chooseAllInputBudget_polynomial chooseCoefficient chooseDegree).add hTail).add
    (PolynomiallyBounded.const 1)

/-- All four native calls and all tape preparation/cleanup terminate on
all random branches of every finite bitstring, including malformed DDH
input and arbitrary raw choose/normalizer replies. The actual first-call
PMF feeds the real continuation; no parser validity or group correctness
is needed for this operational bound. -/
theorem chooseChallengeGuessCompile_haltsWithin_anyInput
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hChoose : ∀ request : List Bool,
      HaltsWithin chooseSource request (chooseCoefficient * (request.length + 1)^chooseDegree))
    (hNormalizer : ∀ request : List Bool,
      HaltsWithin normalizeSource request (normalizationCoefficient * (request.length + 1)^normalizationDegree))
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (input : List Bool) :
    HaltsWithin (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource) input
      (chooseChallengeAllInputBudget chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
        multiplyCoefficient multiplyDegree guessCoefficient guessDegree input.length) := by
  let start := Configuration.initial input
  let q := fun m => chooseCoefficient * (m + 1)^chooseDegree
  let requestLimit := 20000003 * (input.length + 1)
  let chooseTime := chooseCoefficient * (requestLimit + 1)^chooseDegree
  let retainedSize := 100 * (requestLimit + chooseTime + 1)
  let firstTime := chooseAllInputBudget chooseCoefficient chooseDegree input.length
  let tailTime := normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree retainedSize
  let stageDist := evalConfigWithin (chooseCompile chooseSource) start firstTime
  let continuation : Configuration → PMF Bool := fun c =>
    (evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
      (c.resumeAt 0) tailTime).map Configuration.halted
  have hObserve (c d : Configuration) (h : c.Equivalent d) : continuation c = continuation d := by
    apply evalConfigWithin_map_eq_of_equivalent
      (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource) (c.resumeAt 0) (d.resumeAt 0) _ tailTime
      Configuration.halted (fun _ _ h => h.2.1)
    exact (h.withPc 0).withHalted false
  obtain ⟨request, sourceSaved, targetSaved, hLength, hPrefix, hFuture⟩ :=
    chooseCompile_evalObservation_anyInput_bounded chooseSource chooseCoefficient chooseDegree hChoose
      input continuation hObserve
  let returned := fun c => {
    (rawResultFrom chooseSource request sourceSaved (none :: targetSaved) c).swapTapes
    with pc := 119 + (rawCompileOpposite chooseSource).length + 1, halted := true }
  let sourceDist := evalConfigWithin chooseSource (preparedSource request) (q request.length)
  have hRequest : request.length ≤ requestLimit := hLength
  have hSourceTime : q request.length ≤ chooseTime :=
    Nat.mul_le_mul_left chooseCoefficient
      (Nat.pow_le_pow_left (Nat.add_le_add_right hRequest 1) chooseDegree)
  have hRaw (c : Configuration) (hc : c ∈ sourceDist.support) : continuation (returned c) = PMF.pure true := by
    have hSourceStorage := sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    have hInitial := preparedSource_sourceStorage_le request
    have hReturned := rawResultFrom_sourceStorage_le chooseSource request sourceSaved (none :: targetSaved) c
    have hStorage : sourceStorage (returned c) ≤ retainedSize := by
      change sourceStorage c ≤ sourceStorage (preparedSource request) + q request.length at hSourceStorage
      change sourceSaved.length + (none :: targetSaved).length ≤ requestLimit at hPrefix
      have hReturnStorage : sourceStorage (returned c) =
          sourceStorage (rawResultFrom chooseSource request sourceSaved (none :: targetSaved) c) := by
        simp only [returned, sourceStorage, Configuration.swapTapes, Nat.add_comm]
      rw [hReturnStorage]
      change _ ≤ 100 * (requestLimit + chooseTime + 1)
      omega
    have hSmall := normalizationChallengeGuessCompile_haltsFrom_retainedReply
      normalizeSource multiplySource guessSource normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree hNormalizer hMultiply hGuess
      targetSaved (returned c).outputTape.left c.outputBits
      (2 * c.outputTape.cells + 2 - c.outputBits.length) 0
    change ∀ d, PaddedRunsFor (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
      ((returned c).resumeAt 0) d
      (normalizationChallengeRetainedBudget normalizationCoefficient normalizationDegree
        multiplyCoefficient multiplyDegree guessCoefficient guessDegree (sourceStorage (returned c))) → d.halted = true at hSmall
    have hBudget := normalizationChallengeRetainedBudget_monotone
      normalizationCoefficient normalizationDegree multiplyCoefficient multiplyDegree guessCoefficient guessDegree hStorage
    have hStop (d : Configuration)
        (run : PaddedRunsFor (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
          ((returned c).resumeAt 0) d tailTime) : d.halted = true := by
      have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
      rw [evalConfigWithin_eq_of_le _ _ _ _ hBudget hSmall] at hMem
      exact hSmall d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
    dsimp only [continuation]
    calc
      _ = (evalConfigWithin (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
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
  have hFirst := chooseCompile_haltsWithin_anyInput chooseSource chooseCoefficient chooseDegree hChoose input
  have hSecond (c : Configuration) (hc : c ∈ stageDist.support) (d : Configuration)
      (run : PaddedRunsFor (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource)
        (c.resumeAt 0) d tailTime) : d.halted = true := by
    have hm : d.halted ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_pure_iff] at hm
    exact hm
  have hLaw := Program.evalConfigWithin_twoStages_configuration (chooseCompile chooseSource)
    (normalizationChallengeGuessCompile normalizeSource multiplySource guessSource) start rfl rfl firstTime tailTime hFirst hSecond
  change evalConfigWithin (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource) start
    (firstTime + (tailTime + 1)) = _ at hLaw
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  change finish ∈ (evalConfigWithin (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource) start
    (firstTime + tailTime + 1)).support at hMem
  rw [Nat.add_assoc, hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
  rw [PMF.mem_support_map_iff] at hFinish
  obtain ⟨target, _hTarget, rfl⟩ := hFinish
  rfl

/-- The fixed native simulator is polynomial time whenever all four fixed
component programs have all-input polynomial stopping certificates. -/
theorem chooseChallengeGuessCompile_polynomialTime_of_monomials
    (chooseSource normalizeSource multiplySource guessSource : Program)
    (chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hChoose : ∀ request : List Bool,
      HaltsWithin chooseSource request (chooseCoefficient * (request.length + 1)^chooseDegree))
    (hNormalizer : ∀ request : List Bool,
      HaltsWithin normalizeSource request (normalizationCoefficient * (request.length + 1)^normalizationDegree))
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree)) :
    PolynomialTime (chooseChallengeGuessCompile chooseSource normalizeSource multiplySource guessSource) :=
  ⟨chooseChallengeAllInputBudget chooseCoefficient chooseDegree normalizationCoefficient normalizationDegree
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree,
    chooseChallengeAllInputBudget_polynomial _ _ _ _ _ _ _ _,
    chooseChallengeGuessCompile_haltsWithin_anyInput _ _ _ _ _ _ _ _ _ _ _ _ hChoose hNormalizer hMultiply hGuess⟩

end Machine.GuardedCompiler
