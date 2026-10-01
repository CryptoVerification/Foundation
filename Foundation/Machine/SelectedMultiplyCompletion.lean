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

end Machine.GuardedCompiler
