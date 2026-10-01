import Foundation.Machine.MultiplyGuessCompletion

namespace Machine.GuardedCompiler

/-- Frame the saved selected message, restore/frame the final DDH operand,
and run the multiplication/guess/finalization continuation on those tapes. -/
def messageMultiplyGuessCompile (multiplySource guessSource : Program) : Program :=
  let pre := prepareMultiplyMessage.asSubroutine 0 (prepareMultiplyMessage.length + 1)
  let call := operandsMultiplyGuessCompile multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

/-- Start at the actual selected-message return. The public prefix and both
operands are assembled by native code before either embedded source call. -/
def selectedMultiplyGuessCompile (multiplySource guessSource : Program) : Program :=
  let pre := prepareMultiplyPrefix.asSubroutine 0 (prepareMultiplyPrefix.length + 1)
  let call := messageMultiplyGuessCompile multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

theorem messageMultiplyGuessCompile_length (multiplySource guessSource : Program) :
    (messageMultiplyGuessCompile multiplySource guessSource).length =
      68 * multiplySource.length + 68 * guessSource.length + 1113 := by
  simp only [messageMultiplyGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, operandsMultiplyGuessCompile_length,
    show prepareMultiplyMessage.length = 83 from rfl, List.length_cons, List.length_nil]
  omega

theorem selectedMultiplyGuessCompile_length (multiplySource guessSource : Program) :
    (selectedMultiplyGuessCompile multiplySource guessSource).length =
      68 * multiplySource.length + 68 * guessSource.length + 1180 := by
  simp only [selectedMultiplyGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, messageMultiplyGuessCompile_length,
    show prepareMultiplyPrefix.length = 64 from rfl, List.length_cons, List.length_nil]
  omega

/-- The tail of the framed nonempty DDH tuple, after its first header bit.
This is a specification of existing tape cells, not an instruction. -/
def multiplyTupleTail (first second last : List Bool) : List Bool :=
  let tuple := FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last
  List.replicate (tuple.length - 1) true ++ false :: tuple

/-- Exact charged continuation budget, including the message-framing stage
and the final halt at each native subroutine boundary. Source budgets use
their actual request lengths, without a monotonicity assumption. -/
def messageMultiplyGuessBudget (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (chooseResult normalizeResult : Configuration) : Nat :=
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let canonical := canonicalMessageBits message₀ message₁ state
  let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
    instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
  prepareMultiplyMessageSteps n instanceBits (multiplyTupleTail first second last) reply canonical selected +
    (prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected +
      (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1) + 1) + 1)

def selectedMultiplyGuessBudget (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state product : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) : Nat :=
  prepareMultiplyPrefixSteps n instanceBits (multiplyTupleTail first second last) reply
    (selectedMessageConsumed message₀ message₁ challenge) +
    (messageMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state (if challenge then message₁ else message₀)
      product chooseResult normalizeResult + 1)

private theorem halted_of_result (p : Program) (start : Configuration) (steps : Nat)
    (law : PMF (List Bool))
    (h : (evalConfigWithin p start steps).map (fun c => (c.halted, c.outputBits)) =
      law.map (fun bits => (true, bits))) :
    ∀ c, PaddedRunsFor p start c steps → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, hc, rfl⟩
  rw [h, PMF.mem_support_map_iff] at hm
  obtain ⟨bits, _hb, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

/-- Ordinary execution from the actual prefix-stage return. Message framing
passes its complete result directly to operand restoration; no fresh input
configuration is inserted between the native stages. -/
theorem messageMultiplyGuessCompile_correct
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hMultiply : HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).length))
    (correct : evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).length) =
        PMF.pure (some product))
    (hGuess : HaltsWithin guessSource (guessFromProductRequest n instanceBits second state product)
      (qGuess (guessFromProductRequest n instanceBits second state product).length)) :
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    (evalConfigWithin (messageMultiplyGuessCompile multiplySource guessSource)
      (prepareMultiplyMessageStart before savedOutput n instanceBits (multiplyTupleTail first second last)
        reply (canonicalMessageBits message₀ message₁ state) selected blanks)
      (messageMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
        first second last reply message₀ message₁ state selected product chooseResult normalizeResult)).map
          (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  let savedOutput := some challenge :: savedOutputBlocks
    (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
  let canonical := canonicalMessageBits message₀ message₁ state
  let start := prepareMultiplyMessageStart before savedOutput n instanceBits
    (multiplyTupleTail first second last) reply canonical selected blanks
  let finish := prepareMultiplyMessageFinish before savedOutput n instanceBits
    (multiplyTupleTail first second last) reply canonical selected blanks
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
    instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
  let t₁ := prepareMultiplyMessageSteps n instanceBits (multiplyTupleTail first second last) reply canonical selected
  let t₂ := prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected +
    (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1) + 1)
  have hEval : evalConfigWithin prepareMultiplyMessage start t₁ = PMF.pure finish :=
    prepareMultiplyMessage_eval _ _ _ _ _ _ _ _ _
  have hLayout : finish.resumeAt 0 = prepareMultiplyOperandsStart before savedOutput
      (List.replicate ((blanks - 1) - selected.length) none)
      n instanceBits first second last reply canonical selected :=
    prepareMultiplyMessageFinish_operands_layout _ _ _ _ _ _ _ _ _ _ _
  have hCall := operandsMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess
    chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state selected product
    challenge chooseResult normalizeResult ((blanks - 1) - selected.length) hMultiply correct hGuess
  have hSecond : ∀ d, PaddedRunsFor (operandsMultiplyGuessCompile multiplySource guessSource)
      (finish.resumeAt 0) d t₂ → d.halted = true := by
    rw [hLayout]
    apply halted_of_result _ _ _
      ((evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => [taggedGuessValue c.outputBits == challenge]))
    simpa only [PMF.map_comp, Function.comp_def] using hCall
  have h := Program.evalConfigWithin_twoStages_of_pure prepareMultiplyMessage
    (operandsMultiplyGuessCompile multiplySource guessSource) start finish rfl rfl t₁ t₂ hEval rfl hSecond
  rw [hLayout] at h
  exact h.trans hCall

private theorem selected_tail_layout (before output : List (Option Bool))
    (message₀ message₁ state : List Bool) (blanks : Nat) (challenge : Bool) :
    let c := prepareSelectedMessageFinish before output message₀ message₁ state blanks challenge
    c.inputTape.current :: c.inputTape.right =
      (selectedMessageRemaining message₁ state challenge).map some ++ none :: List.replicate blanks none := by
  dsimp only
  rw [prepareSelectedMessageFinish_input]
  cases selectedMessageRemaining message₁ state challenge <;> simp [Tape.moveRight]

/-- Complete native continuation from a selected message and its retained
random challenge. Its public-prefix, message, operand, multiplication and
guess stages share the original DDH/choose/normalization tapes throughout. -/
theorem selectedMultiplyGuessCompile_correct
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state product : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hMultiply : HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last).length))
    (correct : evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some product))
    (hGuess : HaltsWithin guessSource (guessFromProductRequest n instanceBits second state product)
      (qGuess (guessFromProductRequest n instanceBits second state product).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    (evalConfigWithin (selectedMultiplyGuessCompile multiplySource guessSource)
      ((prepareSelectedMessageFinish saved back message₀ message₁ state blanks challenge).resumeAt 0)
      (selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
        first second last reply message₀ message₁ state product challenge chooseResult normalizeResult)).map
          (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
  let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
  let returned := prepareSelectedMessageFinish saved back message₀ message₁ state blanks challenge
  let selected := if challenge then message₁ else message₀
  let consumed := selectedMessageConsumed message₀ message₁ challenge
  let finish := prepareMultiplyPrefixFinish before (none :: some challenge :: back) n instanceBits
    (multiplyTupleTail first second last) reply consumed selected returned.inputTape.current returned.inputTape.right
  let t₁ := prepareMultiplyPrefixSteps n instanceBits (multiplyTupleTail first second last) reply consumed
  let t₂ := messageMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
    first second last reply message₀ message₁ state selected product chooseResult normalizeResult
  have hEval : evalConfigWithin prepareMultiplyPrefix (returned.resumeAt 0) t₁ = PMF.pure finish := by
    dsimp only [returned, saved, original]
    rw [selectedMessage_multiplyPrefix_layout]
    exact prepareMultiplyPrefix_eval _ _ _ _ _ _ _ _ _ _
  have hLayout : finish.resumeAt 0 = prepareMultiplyMessageStart before (some challenge :: back)
      n instanceBits (multiplyTupleTail first second last) reply (canonicalMessageBits message₀ message₁ state) selected blanks := by
    have h := prepareMultiplyPrefixFinish_message_layout before (some challenge :: back) n instanceBits
      (multiplyTupleTail first second last) reply consumed (selectedMessageRemaining message₁ state challenge)
      selected blanks returned.inputTape.current returned.inputTape.right
      (selected_tail_layout saved back message₀ message₁ state blanks challenge)
    dsimp only [consumed] at h
    simpa only [selectedMessage_partition] using h
  have hCall := messageMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess
    chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state selected product
    challenge chooseResult normalizeResult blanks hMultiply correct hGuess
  have hSecond : ∀ d, PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource)
      (finish.resumeAt 0) d t₂ → d.halted = true := by
    rw [hLayout]
    apply halted_of_result _ _ _
      ((evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => [taggedGuessValue c.outputBits == challenge]))
    simpa only [PMF.map_comp, Function.comp_def] using hCall
  have h := Program.evalConfigWithin_twoStages_of_pure prepareMultiplyPrefix
    (messageMultiplyGuessCompile multiplySource guessSource) (returned.resumeAt 0) finish rfl rfl t₁ t₂ hEval rfl hSecond
  rw [hLayout] at h
  exact h.trans hCall

/-- Every branch of the same selected-message continuation halts at the
common bound, since its final observation has a halted single-bit result. -/
theorem selectedMultiplyGuessCompile_correct_haltsFrom
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state product : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) (blanks : Nat)
    (hMultiply : HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last).length))
    (correct : evalWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame (if challenge then message₁ else message₀) ++ frame last).length) =
        PMF.pure (some product))
    (hGuess : HaltsWithin guessSource (guessFromProductRequest n instanceBits second state product)
      (qGuess (guessFromProductRequest n instanceBits second state product).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: multiplyTupleTail first second last
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    ∀ c, PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource)
      ((prepareSelectedMessageFinish saved back message₀ message₁ state blanks challenge).resumeAt 0) c
      (selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
        first second last reply message₀ message₁ state product challenge chooseResult normalizeResult) → c.halted = true := by
  dsimp only
  apply halted_of_result _ _ _
    ((evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
      (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
        (fun c => [taggedGuessValue c.outputBits == challenge]))
  simpa only [PMF.map_comp, Function.comp_def] using
    selectedMultiplyGuessCompile_correct multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
      before n instanceBits first second last reply message₀ message₁ state product challenge chooseResult normalizeResult blanks
      hMultiply correct hGuess

/-- Polynomial overhead for the complete selected-message continuation.
Both source time functions are evaluated at their actual request lengths.
Retained choose/normalizer scratch storage is included in the size factor;
the multiplication scratch has already been bounded by its actual steps. -/
theorem selectedMultiplyGuessBudget_bound (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state product : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) :
    let selected := if challenge then message₁ else message₀
    let multiplyRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
    let guessRequest := guessFromProductRequest n instanceBits second state product
    let size := n + instanceBits.length + first.length + second.length + last.length + reply.length +
      message₀.length + message₁.length + state.length + selected.length + product.length +
      multiplyRequest.length + guessRequest.length + chooseRequest.length + normalizeRequest.length +
      sourceStorage chooseResult + sourceStorage normalizeResult + 1
    selectedMultiplyGuessBudget qMultiply qGuess chooseRequest normalizeRequest n instanceBits
      first second last reply message₀ message₁ state product challenge chooseResult normalizeResult ≤
      20000 * size * (qMultiply multiplyRequest.length + qGuess guessRequest.length + 1)^2 := by
  dsimp only
  let selected := if challenge then message₁ else message₀
  let multiplyRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let guessRequest := guessFromProductRequest n instanceBits second state product
  let canonical := canonicalMessageBits message₀ message₁ state
  let consumed := selectedMessageConsumed message₀ message₁ challenge
  let tupleTail := multiplyTupleTail first second last
  let size := n + instanceBits.length + first.length + second.length + last.length + reply.length +
    message₀.length + message₁.length + state.length + selected.length + product.length +
    multiplyRequest.length + guessRequest.length + chooseRequest.length + normalizeRequest.length +
    sourceStorage chooseResult + sourceStorage normalizeResult + 1
  let time := qMultiply multiplyRequest.length + qGuess guessRequest.length + 1
  have hSize : 1 ≤ size := by dsimp [size]; omega
  have hTime : 1 ≤ time := by dsimp [time]; omega
  have hPow : 1 ≤ time^2 := Nat.one_le_pow _ _ hTime
  have hM : (qMultiply multiplyRequest.length + 1)^2 ≤ time^2 :=
    Nat.pow_le_pow_left (by dsimp [time]; omega) 2
  have hG : (qGuess guessRequest.length + 1)^2 ≤ time^2 :=
    Nat.pow_le_pow_left (by dsimp [time]; omega) 2
  have hConsumed := selectedMessageConsumed_length_le message₀ message₁ state challenge
  change consumed.length ≤ canonical.length at hConsumed
  conv at hConsumed => rhs; simp [canonical, canonicalMessageBits, FiniteBitEncoding.delimit_length]
  have hPrefix := prepareMultiplyPrefix_steps_le n instanceBits tupleTail reply consumed
  have hPrefixScaled : prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed ≤ 300 * size := by
    conv at hPrefix => rhs; simp [tupleTail, multiplyTupleTail, encodeSecurityParameter,
      frame, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hMessage := prepareMultiplyMessage_steps_le n instanceBits tupleTail reply canonical selected
  have hMessageScaled : prepareMultiplyMessageSteps n instanceBits tupleTail reply canonical selected ≤ 200 * size := by
    conv at hMessage => rhs; simp [tupleTail, multiplyTupleTail, canonical, canonicalMessageBits,
      encodeSecurityParameter, frame, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hOperands := prepareMultiplyOperands_steps_le n instanceBits first second last reply canonical selected
  have hOperandsScaled : prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected ≤ 200 * size := by
    conv at hOperands => rhs; simp [canonical, canonicalMessageBits, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hCall := storedFramedCallTraceBudget_bound qMultiply last reply canonical selected multiplyRequest
  have hCallSize : last.length + reply.length + canonical.length + selected.length + multiplyRequest.length + 1 ≤ 5 * size := by
    simp [canonical, canonicalMessageBits, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hCallScaled : storedFramedCallTraceBudget qMultiply last reply canonical selected multiplyRequest ≤
      1125 * size * time^2 := by
    calc
      _ ≤ 225 * (last.length + reply.length + canonical.length + selected.length + multiplyRequest.length + 1) *
          (qMultiply multiplyRequest.length + 1)^2 := hCall
      _ ≤ 225 * (5 * size) * time^2 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hCallSize) hM
      _ = _ := by ring
  have hGuess := guessFromProductBudget_bound qGuess n instanceBits first second last reply message₀ message₁ state selected product
  have hGuessSize : n + instanceBits.length + first.length + second.length + last.length + reply.length +
      message₀.length + message₁.length + state.length + selected.length + product.length + 1 ≤ size := by
    dsimp only [size]
    omega
  have hGuessScaled : guessFromProductBudget qGuess n instanceBits first second last reply message₀ message₁ state selected product ≤
      3000 * size * time^2 := by
    exact hGuess.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hGuessSize) hG)
  let terminal := 20 * (guessRequest.length + multiplyRequest.length + chooseRequest.length + normalizeRequest.length +
    (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).length + selected.length +
    sourceStorage chooseResult + sourceStorage normalizeResult +
    (2 * multiplyRequest.length + 2 + qMultiply multiplyRequest.length) +
    (2 * guessRequest.length + 2 + qGuess guessRequest.length) + 1) + 200 + 1
  have hTerminalLinear : terminal + 4 ≤ 200 * size + 20 * time + 325 := by
    simp only [terminal, List.length_cons, List.length_append, FiniteBitEncoding.delimit_length]
    dsimp only [size, time]
    omega
  have hSizePow : size ≤ size * time^2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left size hPow
  have hTimePow : time ≤ size * time^2 := by
    have ht : time ≤ time^2 := by nlinarith only [hTime]
    exact ht.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (time^2) hSize)
  have hTotalPos : 1 ≤ size * time^2 := (Nat.mul_le_mul hSize hPow)
  have hTerminalScaled : terminal + 4 ≤ 1000 * size * time^2 := by
    have hs := Nat.mul_le_mul_left 200 hSizePow
    have ht := Nat.mul_le_mul_left 20 hTimePow
    have hp := Nat.mul_le_mul_left 325 hTotalPos
    simp only [Nat.mul_assoc] at hs ht hp ⊢
    omega
  have hPrefixPow := hPrefixScaled.trans (Nat.mul_le_mul_left 300 hSizePow)
  have hMessagePow := hMessageScaled.trans (Nat.mul_le_mul_left 200 hSizePow)
  have hOperandsPow := hOperandsScaled.trans (Nat.mul_le_mul_left 200 hSizePow)
  change prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed +
    (prepareMultiplyMessageSteps n instanceBits tupleTail reply canonical selected +
      (prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected +
        (storedFramedCallTraceBudget qMultiply last reply canonical selected multiplyRequest +
          (guessFromProductBudget qGuess n instanceBits first second last reply message₀ message₁ state selected product + terminal + 1) + 1) + 1) + 1) ≤
      20000 * size * time^2
  simp only [Nat.mul_assoc] at hCallScaled hGuessScaled hTerminalScaled ⊢
  omega

/-- The real message and operand preparation are charged before the
all-input multiplication/guess stopping envelope. Storage growth is bounded
by those actual native transitions, including malformed-input scans. -/
def messageMultiplyGuessRetainedBudget
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage : Nat) : Nat :=
  let prepareTime := 1000000000000000000000000000000 * (storage + 1)
  prepareTime + multiplyGuessRetainedSuffixBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
    (storage + prepareTime) + 2

theorem messageMultiplyGuessRetainedBudget_polynomial_of_profile
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n =>
      messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree (size n)) := by
  have hPrepare := (PolynomiallyBounded.const 1000000000000000000000000000000).mul
    (hSize.add (PolynomiallyBounded.const 1))
  have hCall := multiplyGuessRetainedSuffixBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (hSize.add hPrepare)
  exact (hPrepare.add hCall).add (PolynomiallyBounded.const 2)

theorem messageMultiplyGuessRetainedBudget_polynomial
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    PolynomiallyBounded
      (messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) :=
  messageMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree PolynomiallyBounded.id

theorem messageMultiplyGuessRetainedBudget_monotone
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    Monotone (messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) := by
  intro a b h
  have hPrepare := Nat.mul_le_mul_left 1000000000000000000000000000000 (Nat.add_le_add_right h 1)
  have hCall := multiplyGuessRetainedSuffixBudget_monotone
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (Nat.add_le_add h hPrepare)
  exact Nat.add_le_add_right (Nat.add_le_add hPrepare hCall) 2

/-- Start at the actual three retained raw blocks after public-prefix
preparation. The message and operand constructors execute on their real
returned tapes, then both native calls and guess finalization halt on every
branch. No raw field is required to have a valid cryptographic encoding. -/
theorem messageMultiplyGuessCompile_haltsFrom_retained_frontiers
    (multiplySource guessSource : Program)
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    (hMultiply : ∀ request : List Bool,
      HaltsWithin multiplySource request (multiplyCoefficient * (request.length + 1)^multiplyDegree))
    (hGuess : ∀ request : List Bool,
      HaltsWithin guessSource request (guessCoefficient * (request.length + 1)^guessDegree))
    (before savedOutput : List (Option Bool))
    (originalPrefix original reply canonical : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    let start := seekStoredInputScratchStart
      (originalPrefix.reverse.map some ++ none :: before) original reply canonical inputBlanks output
    ∀ finish, PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) start finish
      (messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  let start := seekStoredInputScratchStart
    (originalPrefix.reverse.map some ++ none :: before) original reply canonical inputBlanks output
  let storage := sourceStorage start
  let prepareTime := 1000000000000000000000000000000 * (storage + 1)
  let callTime := multiplyGuessRetainedSuffixBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
    (storage + prepareTime)
  obtain ⟨messageFinish, operandFinish, messageTime, operandTime, saved, remaining,
    moves, selected, remainingInput, hTime, messageRun, messageHalt, operandRun,
    operandHalt, _hMoves, hOutput, hCurrent, hRight⟩ :=
    prepareMultiplyMessage_operands_terminate_with_input_output_layout
      before savedOutput originalPrefix original reply canonical inputBlanks outputBlanks
  let restored := restoreInputBeforeScratchFinish before (originalPrefix ++ original)
    reply canonical selected (List.replicate remainingInput none) {}
  let cells := (originalPrefix ++ original).map some ++ none :: reply.map some ++
    none :: canonical.map some ++ none :: selected.map some ++ none :: List.replicate remainingInput none
  have hRaw : restored.inputTape.current :: restored.inputTape.right = cells := by
    cases hOriginal : originalPrefix ++ original <;>
      simp [restored, cells, restoreInputBeforeScratchFinish, restoreStoredInputFinish,
        Tape.moveRight, hOriginal, List.append_assoc]
  have hMoved : ∀ i,
      (((Tape.moveRight^[moves]) restored.inputTape).current ::
        ((Tape.moveRight^[moves]) restored.inputTape).right).getD i none = (cells.drop moves).getD i none := by
    intro i
    rw [moveRight_iterate_remaining, hRaw]
    split
    · rename_i hEmpty
      simp [hEmpty]
    · rfl
  have hCells : ∀ i, (operandFinish.inputTape.current :: operandFinish.inputTape.right).getD i none =
      (cells.drop moves).getD i none := by
    intro i
    have hPhysical : (operandFinish.inputTape.current :: operandFinish.inputTape.right).getD i none =
        (((Tape.moveRight^[moves]) restored.inputTape).current ::
          ((Tape.moveRight^[moves]) restored.inputTape).right).getD i none := by
      cases i with
      | zero => simpa only [List.getD_cons_zero] using hCurrent
      | succ i => simpa only [List.getD_cons_succ] using hRight i
    exact hPhysical.trans (hMoved i)
  have hPrepare : messageTime + operandTime ≤ prepareTime := by
    change messageTime + operandTime ≤ 1000000000000000000000000000000 * storage +
      1000000000000000000000000000000 at hTime
    dsimp only [prepareTime]
    omega
  have hMessageStorage := sourceStorage_le_of_run messageRun
  have hOperandStorage := sourceStorage_le_of_run operandRun
  have hStorage : sourceStorage operandFinish ≤ storage + prepareTime := by
    change sourceStorage messageFinish ≤ storage + messageTime at hMessageStorage
    change sourceStorage operandFinish ≤ sourceStorage messageFinish + operandTime at hOperandStorage
    omega
  have hCallsSmall := multiplyThenGuessCompile_haltsFrom_retained_suffix multiplySource guessSource
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hMultiply hGuess
    operandFinish.inputTape saved remaining (originalPrefix ++ original) reply canonical selected remainingInput moves hCells
  have hActual :
      ({ inputTape := operandFinish.inputTape,
         outputTape := { left := saved, right := List.replicate remaining none } } : Configuration) =
      operandFinish.resumeAt 0 := by
    simp only [Configuration.resumeAt, hOutput]
  rw [hActual] at hCallsSmall
  have hCallsBound := multiplyGuessRetainedSuffixBudget_monotone
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hStorage
  have hCalls (finish : Configuration)
      (run : PaddedRunsFor (multiplyThenGuessCompile multiplySource guessSource) (operandFinish.resumeAt 0) finish callTime) :
      finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [evalConfigWithin_eq_of_le _ _ _ _ hCallsBound hCallsSmall] at hMem
    exact hCallsSmall finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hOperandEval := operandRun.evalConfigWithin_eq_pure_of_no_randomBit prepareMultiplyOperands_no_randomBit
  have hOperandFirst := operandRun.haltsFrom_of_no_randomBit operandHalt prepareMultiplyOperands_no_randomBit
    (Nat.le_refl operandTime)
  have hOperandSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareMultiplyOperands (messageFinish.resumeAt 0) operandTime).support)
      (d : Configuration)
      (run : PaddedRunsFor (multiplyThenGuessCompile multiplySource guessSource) (c.resumeAt 0) d callTime) :
      d.halted = true := by
    rw [hOperandEval, PMF.mem_support_pure_iff] at hc
    subst c
    exact hCalls d run
  have hOperandLaw := Program.evalConfigWithin_twoStages_configuration prepareMultiplyOperands
    (multiplyThenGuessCompile multiplySource guessSource) (messageFinish.resumeAt 0) rfl rfl
    operandTime callTime hOperandFirst hOperandSecond
  change evalConfigWithin (operandsMultiplyGuessCompile multiplySource guessSource) (messageFinish.resumeAt 0)
    (operandTime + (callTime + 1)) = _ at hOperandLaw
  have hOperandStop (finish : Configuration)
      (run : PaddedRunsFor (operandsMultiplyGuessCompile multiplySource guessSource) (messageFinish.resumeAt 0) finish
        (operandTime + (callTime + 1))) : finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [hOperandLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
    rw [PMF.mem_support_map_iff] at hFinish
    obtain ⟨target, _hTarget, rfl⟩ := hFinish
    rfl
  have hMessageEval := messageRun.evalConfigWithin_eq_pure_of_no_randomBit prepareMultiplyMessage_no_randomBit
  have hMessageFirst := messageRun.haltsFrom_of_no_randomBit messageHalt prepareMultiplyMessage_no_randomBit
    (Nat.le_refl messageTime)
  have hMessageSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareMultiplyMessage start messageTime).support)
      (d : Configuration)
      (run : PaddedRunsFor (operandsMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) d
        (operandTime + (callTime + 1))) : d.halted = true := by
    rw [hMessageEval, PMF.mem_support_pure_iff] at hc
    subst c
    exact hOperandStop d run
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareMultiplyMessage
    (operandsMultiplyGuessCompile multiplySource guessSource) start rfl rfl
    messageTime (operandTime + (callTime + 1)) hMessageFirst hMessageSecond
  change evalConfigWithin (messageMultiplyGuessCompile multiplySource guessSource) start
    (messageTime + ((operandTime + (callTime + 1)) + 1)) = _ at hLaw
  have hSmall (finish : Configuration)
      (run : PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) start finish
        (messageTime + ((operandTime + (callTime + 1)) + 1))) : finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [hLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
    rw [PMF.mem_support_map_iff] at hFinish
    obtain ⟨target, _hTarget, rfl⟩ := hFinish
    rfl
  have hBound : messageTime + ((operandTime + (callTime + 1)) + 1) ≤
      messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage := by
    change messageTime + ((operandTime + (callTime + 1)) + 1) ≤ prepareTime + callTime + 2
    omega
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall] at hMem
  exact hSmall finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)


/-- Charge the real prefix restoration before the malformed raw-block
message/multiply/guess continuation. The fixture's conservative size bound
comes from the retained cells of that restoration, not a free tape reset. -/
def selectedMultiplyGuessRetainedBudget
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage : Nat) : Nat :=
  200000 * (storage + 1) +
    messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
      (10000000 * (storage + 1)) + 1

theorem selectedMultiplyGuessRetainedBudget_polynomial_of_profile
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat)
    {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n =>
      selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree (size n)) := by
  have hSuccessor := hSize.add (PolynomiallyBounded.const 1)
  have hPrepare := (PolynomiallyBounded.const 200000).mul hSuccessor
  have hContinuation := messageMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree
    ((PolynomiallyBounded.const 10000000).mul hSuccessor)
  exact (hPrepare.add hContinuation).add (PolynomiallyBounded.const 1)

theorem selectedMultiplyGuessRetainedBudget_polynomial
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    PolynomiallyBounded
      (selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) :=
  selectedMultiplyGuessRetainedBudget_polynomial_of_profile
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree PolynomiallyBounded.id

theorem selectedMultiplyGuessRetainedBudget_monotone
    (multiplyCoefficient multiplyDegree guessCoefficient guessDegree : Nat) :
    Monotone (selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree) := by
  intro a b h
  have hSuccessor := Nat.add_le_add_right h 1
  have hPrepare := Nat.mul_le_mul_left 200000 hSuccessor
  have hContinuation := messageMultiplyGuessRetainedBudget_monotone
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (Nat.mul_le_mul_left 10000000 hSuccessor)
  exact Nat.add_le_add_right (Nat.add_le_add hPrepare hContinuation) 1

/-- Native prefix preparation followed by the full multiplication/guess
continuation stops on every branch even when the selected response is an
arbitrary finite raw bitstring. Both embedded programs halt on all of their
actual requests. The caller's saved input and output prefixes are retained. -/
theorem selectedMultiplyGuessCompile_haltsFrom_raw_frontier
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
    ∀ finish, PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource) start finish
      (selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
        (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let start : Configuration :=
    { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let storage := sourceStorage start
  let continuationTime := messageMultiplyGuessRetainedBudget
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree (10000000 * (storage + 1))
  obtain ⟨prepared, used, before, originalPrefix, original, reply, canonical, after, remaining,
    hTime, run, hHalt, hEquivalent, hFixtureSize⟩ :=
    prepareMultiplyPrefix_terminates_with_retained_frontiers input savedOutput outputBlanks raw inputBlanks hForward
  let fixture := seekStoredInputScratchStart
    (originalPrefix.reverse.map some ++ none :: before) original reply canonical 0
    { left := after, right := List.replicate remaining none }
  have hMessage := messageMultiplyGuessCompile_haltsFrom_retained_frontiers multiplySource guessSource
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hMultiply hGuess
    before after originalPrefix original reply canonical 0 remaining
  have hMessageTime := messageMultiplyGuessRetainedBudget_monotone
    multiplyCoefficient multiplyDegree guessCoefficient guessDegree hFixtureSize
  change messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
    (sourceStorage fixture) ≤ continuationTime at hMessageTime
  change ∀ finish, PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) fixture finish
    (messageMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree
      (sourceStorage fixture)) → finish.halted = true at hMessage
  have hFixtureStop (finish : Configuration)
      (run : PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) fixture finish continuationTime) :
      finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [evalConfigWithin_eq_of_le _ _ _ _ hMessageTime hMessage] at hMem
    exact hMessage finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hContinuation (finish : Configuration)
      (run : PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) (prepared.resumeAt 0) finish continuationTime) :
      finish.halted = true := by
    have hMem : finish.halted ∈ ((evalConfigWithin (messageMultiplyGuessCompile multiplySource guessSource)
        (prepared.resumeAt 0) continuationTime).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [evalConfigWithin_map_eq_of_equivalent _ _ _ hEquivalent _ Configuration.halted
      (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hMem
    obtain ⟨target, hTarget, hEq⟩ := hMem
    exact hEq.symm.trans (hFixtureStop target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))
  have hFirst := run.haltsFrom_of_no_randomBit hHalt prepareMultiplyPrefix_no_randomBit (Nat.le_refl used)
  have hEval := run.evalConfigWithin_eq_pure_of_no_randomBit prepareMultiplyPrefix_no_randomBit
  have hSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareMultiplyPrefix start used).support)
      (d : Configuration)
      (tailRun : PaddedRunsFor (messageMultiplyGuessCompile multiplySource guessSource) (c.resumeAt 0) d continuationTime) :
      d.halted = true := by
    rw [hEval, PMF.mem_support_pure_iff] at hc
    subst c
    exact hContinuation d tailRun
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareMultiplyPrefix
    (messageMultiplyGuessCompile multiplySource guessSource) start rfl rfl used continuationTime hFirst hSecond
  change evalConfigWithin (selectedMultiplyGuessCompile multiplySource guessSource) start
    (used + (continuationTime + 1)) = _ at hLaw
  have hSmall (finish : Configuration)
      (run : PaddedRunsFor (selectedMultiplyGuessCompile multiplySource guessSource) start finish
        (used + (continuationTime + 1))) : finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [hLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
    rw [PMF.mem_support_map_iff] at hFinish
    obtain ⟨target, _hTarget, rfl⟩ := hFinish
    rfl
  have hBound : used + (continuationTime + 1) ≤
      selectedMultiplyGuessRetainedBudget multiplyCoefficient multiplyDegree guessCoefficient guessDegree storage := by
    change used ≤ 200000 * storage + 200000 at hTime
    change used + (continuationTime + 1) ≤ 200000 * (storage + 1) + continuationTime + 1
    omega
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall] at hMem
  exact hSmall finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)

end Machine.GuardedCompiler
