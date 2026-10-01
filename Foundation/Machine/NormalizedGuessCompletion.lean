import Foundation.Machine.SelectedMultiplyCompletion
import Foundation.Machine.NormalizedMessageSelection

namespace Machine.GuardedCompiler

/-- Sample the challenge and copy its selected message before native
request construction, multiplication, guess invocation and finalization.
All stages are fixed bit-machine syntax on the same physical tapes. -/
def normalizedMultiplyGuessCompile (multiplySource guessSource : Program) : Program :=
  let pre := prepareSelectedMessage.asSubroutine 0 (prepareSelectedMessage.length + 1)
  let call := selectedMultiplyGuessCompile multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

theorem normalizedMultiplyGuessCompile_length (multiplySource guessSource : Program) :
    (normalizedMultiplyGuessCompile multiplySource guessSource).length =
      68 * multiplySource.length + 68 * guessSource.length + 1230 := by
  simp only [normalizedMultiplyGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, selectedMultiplyGuessCompile_length,
    show prepareSelectedMessage.length = 47 from rfl, List.length_cons, List.length_nil]
  omega

/-- A single budget covers both native fair-bit branches. The two products
are mathematical specifications of the certified multiplication outputs,
not data inserted into the generated machine code. -/
def normalizedMultiplyGuessTailBudget (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration) : Nat :=
  max
    (selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product false) false chooseResult normalizeResult)
    (selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product true) true chooseResult normalizeResult)

theorem normalizedMultiplyGuessTailBudget_fits (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration) (challenge : Bool) :
    selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product challenge) challenge chooseResult normalizeResult ≤
    normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult := by
  cases challenge
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- The final output law includes the native fair challenge, the actual
certified multiplication calls and the source guess randomness. A common
budget covers both selected-message branches, including early return. -/
theorem normalizedMultiplyGuessCompile_correct
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (correct : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult
    (evalConfigWithin (normalizedMultiplyGuessCompile multiplySource guessSource)
      (prepareMessageSelectionStart saved back message₀ message₁ state blanks)
      (prepareSelectedMessageSteps message₀ message₁ state + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
          (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
  let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
  let start := prepareMessageSelectionStart saved back message₀ message₁ state blanks
  let tailBudget := normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
    first second last reply message₀ message₁ state product chooseResult normalizeResult
  let returned := prepareSelectedMessageFinish saved back message₀ message₁ state blanks
  have hEval : evalConfigWithin prepareSelectedMessage start (prepareSelectedMessageSteps message₀ message₁ state) =
      Foundation.Probability.sampleBit.map returned := prepareSelectedMessage_eval _ _ _ _ _ _
  have hBranch (bit : Bool) :
      (evalConfigWithin (selectedMultiplyGuessCompile multiplySource guessSource) ((returned bit).resumeAt 0) tailBudget).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
        (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == bit])) := by
    have hFits := normalizedMultiplyGuessTailBudget_fits qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult bit
    have hStable := evalConfigWithin_eq_of_le (selectedMultiplyGuessCompile multiplySource guessSource)
      ((returned bit).resumeAt 0) _ tailBudget hFits
      (selectedMultiplyGuessCompile_correct_haltsFrom multiplySource guessSource qMultiply qGuess
        chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state (product bit)
        bit chooseResult normalizeResult blanks (hMultiply bit) (correct bit) (hGuess bit))
    rw [hStable]
    exact selectedMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess
      chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state (product bit)
      bit chooseResult normalizeResult blanks (hMultiply bit) (correct bit) (hGuess bit)
  have hBranchHalts (bit : Bool) : ∀ c, PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource)
      ((returned bit).resumeAt 0) c tailBudget → c.halted = true := by
    intro c run
    have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
      (c.halted, c.outputBits)).mpr ⟨c, hc, rfl⟩
    rw [hBranch bit, PMF.mem_support_map_iff] at hm
    obtain ⟨d, _hd, heq⟩ := hm
    exact (congrArg Prod.fst heq).symm
  have h := Program.evalConfigWithin_twoStages prepareSelectedMessage
    (selectedMultiplyGuessCompile multiplySource guessSource) start rfl rfl
    (prepareSelectedMessageSteps message₀ message₁ state) tailBudget
    (prepareSelectedMessage_haltsFrom _ _ _ _ _ _)
    (by
      intro c hc
      rw [hEval, PMF.mem_support_map_iff] at hc
      obtain ⟨bit, _hb, rfl⟩ := hc
      exact hBranchHalts bit)
  rw [hEval, PMF.bind_map] at h
  simp only [Function.comp_def] at h
  exact h.trans (by simp_rw [hBranch])

/-- Begin at the actual guarded normalizer's returned state, with both
source scratch regions retained. Its certified canonical output supplies
the selector layout; this equality supplies no new machine input load. -/
theorem normalizedMultiplyGuessCompile_fromNormalizer_correct
    (chooseSource normalizeSource multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (chooseSaved : List (Option Bool))
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration)
    (hOutput : normalizeResult.outputBits = canonicalMessageBits message₀ message₁ state)
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (correct : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    let normalReturn := (rawResultFrom normalizeSource normalizeRequest (none :: chooseReturn.outputTape.left)
      (none :: saved) normalizeResult).swapTapes
    let tailBudget := normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult
    (evalConfigWithin (normalizedMultiplyGuessCompile multiplySource guessSource) (normalReturn.resumeAt 0)
      (prepareSelectedMessageSteps message₀ message₁ state + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state (product bit)))
          (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  dsimp only
  rw [rawResultFrom_selectedMessageStart _ _ _ _ _ _ _ _ hOutput,
    normalizerResult_stored_back_layout]
  exact normalizedMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
    before n instanceBits first second last reply message₀ message₁ state product chooseResult normalizeResult
    (2 * normalizeResult.outputTape.cells + 2 - normalizeResult.outputBits.length) hMultiply correct hGuess

/-- Worst-case halting of the same native fair-challenge continuation.
Both challenge choices and all source guess branches are covered. -/
theorem normalizedMultiplyGuessCompile_correct_haltsFrom
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hMultiply : ∀ bit : Bool, HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length))
    (correct : ∀ bit : Bool, evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if bit then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some (product bit)))
    (hGuess : ∀ bit : Bool, HaltsWithin guessSource (guessFromProductRequest n instanceBits second state (product bit))
      (qGuess (guessFromProductRequest n instanceBits second state (product bit)).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult
    ∀ c, PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource)
      (prepareMessageSelectionStart saved back message₀ message₁ state blanks) c
      (prepareSelectedMessageSteps message₀ message₁ state + (tailBudget + 1)) → c.halted = true := by
  dsimp only
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, hc, rfl⟩
  rw [normalizedMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess
    chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state product
    chooseResult normalizeResult blanks hMultiply correct hGuess, PMF.mem_support_bind_iff] at hm
  obtain ⟨bit, _hb, hm⟩ := hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨d, _hd, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

/-- A polynomial majorant for the common fair-challenge tail budget. It
charges both actual multiplication/guess request sizes and both products;
no monotonicity of either source time function is needed. -/
theorem normalizedMultiplyGuessTailBudget_bound (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state : List Bool)
    (product : Bool → List Bool) (chooseResult normalizeResult : Configuration) :
    let selected := fun bit : Bool => if bit then message₁ else message₀
    let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
    let guessRequest := fun bit => guessFromProductRequest n instanceBits second state (product bit)
    let size := fun bit => n + instanceBits.length + first.length + second.length + last.length + reply.length +
      message₀.length + message₁.length + state.length + (selected bit).length + (product bit).length +
      (multiplyRequest bit).length + (guessRequest bit).length + chooseRequest.length + normalizeRequest.length +
      sourceStorage chooseResult + sourceStorage normalizeResult + 1
    normalizedMultiplyGuessTailBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product chooseResult normalizeResult ≤
      20000 * (size false + size true) *
        (qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
          qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1)^2 := by
  dsimp only
  let selected := fun bit : Bool => if bit then message₁ else message₀
  let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
  let guessRequest := fun bit => guessFromProductRequest n instanceBits second state (product bit)
  let size := fun bit => n + instanceBits.length + first.length + second.length + last.length + reply.length +
    message₀.length + message₁.length + state.length + (selected bit).length + (product bit).length +
    (multiplyRequest bit).length + (guessRequest bit).length + chooseRequest.length + normalizeRequest.length +
    sourceStorage chooseResult + sourceStorage normalizeResult + 1
  let time := qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  have hBranch (bit : Bool) : selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product bit) bit chooseResult normalizeResult ≤
      20000 * (size false + size true) * time^2 := by
    have h := selectedMultiplyGuessBudget_bound qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product bit) bit chooseResult normalizeResult
    change selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (product bit) bit chooseResult normalizeResult ≤
        20000 * size bit * (qMultiply (multiplyRequest bit).length + qGuess (guessRequest bit).length + 1)^2 at h
    have hSize : size bit ≤ size false + size true := by cases bit <;> omega
    have hTime : qMultiply (multiplyRequest bit).length + qGuess (guessRequest bit).length + 1 ≤ time := by
      cases bit <;> dsimp only [time] <;> omega
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 20000 hSize) (Nat.pow_le_pow_left hTime 2))
  exact Nat.max_le.mpr ⟨hBranch false, hBranch true⟩


/-- All native selection, prefix restoration, multiplication, guessing and
finalization work is charged against retained storage. This envelope needs
no canonical response or group-operation correctness premise. -/
def normalizedMultiplyGuessRetainedBudget
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage : Nat) : Nat :=
  let selectionTime := 400 * storage + 500
  selectionTime + selectedMultiplyGuessRetainedBudget
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (storage + selectionTime) + 1

theorem normalizedMultiplyGuessRetainedBudget_polynomial_of_profile
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n =>
      normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree (size n)) := by
  have hSelection := ((PolynomiallyBounded.const 400).mul hSize).add (PolynomiallyBounded.const 500)
  have hContinuation := selectedMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (hSize.add hSelection)
  exact (hSelection.add hContinuation).add (PolynomiallyBounded.const 1)

theorem normalizedMultiplyGuessRetainedBudget_polynomial
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    PolynomiallyBounded
      (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) :=
  normalizedMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree PolynomiallyBounded.id

/-- The complete continuation runs directly on arbitrary finite raw
normalization-response cells and the real saved caller tapes. Native
selection's two branches each keep a raw input suffix and a fresh output
frontier, so the whole multiply/guess chain stops on every random branch. -/
theorem normalizedMultiplyGuessCompile_haltsFrom_raw_frontier
    (multiplySource guessSource : Program)
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (input : Tape) (savedOutput : List (Option Bool)) (outputBlanks : Nat)
    (raw : List Bool) (inputBlanks : Nat)
    (hForward : input.current :: input.right = raw.map some ++ none :: List.replicate inputBlanks none) :
    let start : Configuration :=
      { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    ∀ finish, PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) start finish
      (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start : Configuration := { inputTape := input, outputTape := output }
  let storage := sourceStorage start
  let selectionTime := 400 * storage + 500
  let continuationTime := selectedMultiplyGuessRetainedBudget
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (storage + selectionTime)
  have hFirst (c : Configuration) (run : PaddedRunsFor prepareSelectedMessage start c selectionTime) :
      c.halted = true := prepareSelectedMessage_haltsFrom_anyTape input output c run
  have hSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareSelectedMessage start selectionTime).support)
      (d : Configuration)
      (run : PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) d continuationTime) :
      d.halted = true := by
    have selectedRun := (mem_support_evalConfigWithin_iff _ _ _ _).mp hc
    obtain ⟨after, remaining, hOutput⟩ :=
      prepareSelectedMessage_output_layout_anyTape input savedOutput outputBlanks c selectedRun
    obtain ⟨rest, padding, hRest⟩ :=
      prepareSelectedMessage_input_raw_frontier input output raw inputBlanks hForward c selectedRun
    have hSmall := selectedMultiplyGuessCompile_haltsFrom_raw_frontier multiplySource guessSource
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree hMultiply hGuess
      c.inputTape after remaining rest padding hRest
    have hEntry :
        ({ inputTape := c.inputTape,
           outputTape := { left := after, right := List.replicate remaining none } } : Configuration) =
        c.resumeAt 0 := by simp only [Configuration.resumeAt, hOutput]
    rw [hEntry] at hSmall
    have hStorage := sourceStorage_le_of_padded_run selectedRun
    change sourceStorage c ≤ storage + selectionTime at hStorage
    have hTime := selectedMultiplyGuessRetainedBudget_monotone
      multiplyCoefficient multiplyDegree guessCoefficient guessDegree hStorage
    change selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
      (sourceStorage c) ≤ continuationTime at hTime
    change ∀ finish, PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) finish
      (selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage c)) → finish.halted = true at hSmall
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [evalConfigWithin_eq_of_le _ _ _ _ hTime hSmall] at hMem
    exact hSmall d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareSelectedMessage
    (selectedMultiplyGuessCompile multiplySource guessSource) start rfl rfl selectionTime continuationTime hFirst hSecond
  have hFuel : selectionTime + (continuationTime + 1) =
      normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage := by
    change selectionTime + (continuationTime + 1) = selectionTime + continuationTime + 1
    omega
  rw [hFuel] at hLaw
  change evalConfigWithin (normalizedMultiplyGuessCompile multiplySource guessSource) start
    (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage) = _ at hLaw
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
  rw [PMF.mem_support_map_iff] at hFinish
  obtain ⟨target, _hTarget, rfl⟩ := hFinish
  rfl

/-- The guarded normalizer's actual returned configuration satisfies the
raw-frontier interface regardless of its decoded response. All retained
source scratch cells remain part of the storage charged by the bound. -/
theorem normalizedMultiplyGuessCompile_fromNormalizer_haltsFrom_raw
    (normalizer multiplySource guessSource : Program)
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (request : List Bool) (beforeInput savedInput : List (Option Bool)) (result : Configuration) :
    let returned := (rawResultFrom normalizer request beforeInput (none :: savedInput) result).swapTapes
    ∀ finish, PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) (returned.resumeAt 0) finish
      (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage returned)) → finish.halted = true := by
  dsimp only
  exact normalizedMultiplyGuessCompile_haltsFrom_raw_frontier multiplySource guessSource
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hMultiply hGuess
    _ _ 0 [] (2 * result.outputTape.cells + 2 - result.outputBits.length) rfl


theorem normalizedMultiplyGuessRetainedBudget_monotone
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    Monotone (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) := by
  intro a b h
  have hSelection := Nat.add_le_add_right (Nat.mul_le_mul_left 400 h) 500
  have hContinuation := selectedMultiplyGuessRetainedBudget_monotone
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (Nat.add_le_add h hSelection)
  exact Nat.add_le_add_right (Nat.add_le_add hSelection hContinuation) 1

/-- All finite retained prefixes are allowed in a native raw normalizer
return. Its source scratch is a fresh output frontier; its returned bits
remain on the input tape, even if no decoded response is available. -/
theorem normalizedMultiplyGuessCompile_fromRawResult_haltsFrom_raw
    (normalizer multiplySource guessSource : Program)
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (request : List Bool) (sourceSaved targetSaved : List (Option Bool)) (result : Configuration) :
    let returned := (rawResultFrom normalizer request sourceSaved targetSaved result).swapTapes
    ∀ finish, PaddedRunsFor (normalizedMultiplyGuessCompile multiplySource guessSource) (returned.resumeAt 0) finish
      (normalizedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage returned)) → finish.halted = true := by
  dsimp only
  exact normalizedMultiplyGuessCompile_haltsFrom_raw_frontier multiplySource guessSource
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hMultiply hGuess
    _ _ 0 [] (2 * result.outputTape.cells + 2 - result.outputBits.length) rfl

end Machine.GuardedCompiler
