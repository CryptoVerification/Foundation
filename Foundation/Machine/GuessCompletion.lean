import Foundation.Machine.GuessInvocationPreparation
import Foundation.Machine.StoredGuessLayout

namespace Machine.GuardedCompiler

/-- Complete post-multiplication code: construct and invoke the source's
guess request, then process the actual returned tapes and halt with the
single comparison bit. The two block counts describe the fixed protocol. -/
def completedGuessFromProductCompile (source : Program) : Program :=
  let invoke := guessFromProductCompile source
  let pre := invoke.asSubroutine 0 (invoke.length + 1)
  Program.withSubroutine pre (finishStoredGuess 8 4) [.halt]
    (pre.length + (finishStoredGuess 8 4).length + 1)

theorem completedGuessFromProductCompile_length (source : Program) :
    (completedGuessFromProductCompile source).length = 68 * source.length + 685 := by
  simp only [completedGuessFromProductCompile, Program.withSubroutine,
    List.length_append, Program.asSubroutine_length, guessFromProductCompile_length,
    finishStoredGuess_protocol_length, List.length_cons, List.length_nil]

private theorem pair_observe (c d : Configuration) (h : c.Equivalent d) :
    (c.halted, c.outputBits) = (d.halted, d.outputBits) :=
  congrArg₂ Prod.mk h.2.1 h.outputBits

/-- Execute both native stages on the same tapes. The terminal premise is
about the actual guarded raw result, at one common budget for every source
branch. It is discharged below from the retained multiplication layout and
the source's charged storage bound, rather than a new input-loading action. -/
theorem completedGuessFromProductCompile_evalResult (source : Program)
    (before beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) (q : Nat → Nat)
    (halts : HaltsWithin source (guessFromProductRequest n instanceBits second state product)
      (q (guessFromProductRequest n instanceBits second state product).length))
    (terminalBudget : Nat) (challenge : Bool)
    (terminal : ∀ c ∈ (evalConfigWithin source
        (preparedSource (guessFromProductRequest n instanceBits second state product))
        (q (guessFromProductRequest n instanceBits second state product).length)).support,
      (evalConfigWithin (finishStoredGuess 8 4)
        (((rawResultFrom source (guessFromProductRequest n instanceBits second state product)
          (none :: guessFromProductSavedOutput beforeOutput state second product)
          (guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected product)
          c).swapTapes).resumeAt 0) terminalBudget).map (fun d => (d.halted, d.outputBits)) =
        PMF.pure (true, [taggedGuessValue c.outputBits == challenge])) :
    (evalConfigWithin (completedGuessFromProductCompile source)
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product +
        (terminalBudget + 1))).map (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin source (preparedSource (guessFromProductRequest n instanceBits second state product))
        (q (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  let stage := guessFromProductCompile source
  let start := prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding
  let steps := guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product
  let request := guessFromProductRequest n instanceBits second state product
  let sourceDist := evalConfigWithin source (preparedSource request) (q request.length)
  let stageDist := evalConfigWithin stage start steps
  let observe : Configuration → Bool × List Bool := fun c => (c.halted, c.outputBits)
  let continuation : Configuration → PMF (Bool × List Bool) :=
    fun c => (evalConfigWithin (finishStoredGuess 8 4) (c.resumeAt 0) terminalBudget).map observe
  have hObserve : ∀ c d, c.Equivalent d → continuation c = continuation d := by
    intro c d h
    apply evalConfigWithin_map_eq_of_equivalent
    · exact (h.withPc 0).withHalted false
    · exact pair_observe
  have hFuture := guessFromProductCompile_evalObservation source before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding q halts continuation hObserve
  have hBind := congrArg (fun distribution : PMF (PMF (Bool × List Bool)) => distribution.bind id) hFuture
  simp only [PMF.bind_map, Function.comp_def, id_eq] at hBind
  have hContinuation : stageDist.bind continuation =
      sourceDist.map (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
    change stageDist.bind continuation = _ at hBind
    rw [hBind]
    change sourceDist.bind _ = sourceDist.bind _
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext c hc
    exact terminal c hc
  have hSecond : ∀ c ∈ stageDist.support,
      ∀ d, PaddedRunsFor (finishStoredGuess 8 4) (c.resumeAt 0) d terminalBudget → d.halted = true := by
    intro c hc d run
    have hm : observe d ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_map_iff] at hm
    obtain ⟨e, _he, heq⟩ := hm
    exact (congrArg Prod.fst heq).symm
  have h := Program.evalConfigWithin_twoStages stage (finishStoredGuess 8 4) start rfl rfl steps terminalBudget
    (guessFromProductCompile_haltsFrom source before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding q halts)
    hSecond
  exact h.trans hContinuation

/-- Common terminal bound for the actual protocol. Guess storage is bounded
by its prepared input storage plus its actual source transition count; the
other three configurations are the already retained source returns. -/
def completedGuessTerminalBudget (q : Nat → Nat)
    (guessRequest multiplyRequest chooseRequest normalizeRequest body selected : List Bool)
    (chooseResult normalizeResult multiplyResult : Configuration) : Nat :=
  20 * (guessRequest.length + multiplyRequest.length + chooseRequest.length + normalizeRequest.length +
    body.length + selected.length + sourceStorage chooseResult + sourceStorage normalizeResult +
    sourceStorage multiplyResult + (2 * guessRequest.length + 2 + q guessRequest.length) + 1) + 200

private theorem completedGuessTerminalBudget_fits (source : Program) (q : Nat → Nat)
    (guessRequest multiplyRequest chooseRequest normalizeRequest body selected : List Bool)
    (chooseResult normalizeResult multiplyResult guessResult : Configuration)
    (hc : guessResult ∈ (evalConfigWithin source (preparedSource guessRequest) (q guessRequest.length)).support) :
    finishStoredGuessSteps
      (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult) guessResult.outputBits ≤
      completedGuessTerminalBudget q guessRequest multiplyRequest chooseRequest normalizeRequest body selected
        chooseResult normalizeResult multiplyResult := by
  have h := finishStoredGuess_steps_le_sourceStorage guessRequest multiplyRequest chooseRequest normalizeRequest body selected
    chooseResult normalizeResult multiplyResult guessResult
  have hStorage := sourceStorage_le_of_padded_run ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hInitial := preparedSource_sourceStorage_le guessRequest
  dsimp only [completedGuessTerminalBudget]
  omega

/-- Complete native final-bit distribution from the actual guarded multiply
return. The source guess call and cleanup consume that very configuration;
all scratch is charged and every random source branch retains its probability.
No caller supplies a decoded reply or reloads the final challenge. -/
theorem completedGuessFromProductCompile_returnedFrameResult_evalResult
    (multiplySource guessSource : Program) (q : Nat → Nat)
    (multiplyRequest chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (challenge : Bool) (chooseResult normalizeResult multiplyResult : Configuration)
    (halts : HaltsWithin guessSource
      (guessFromProductRequest n instanceBits second state multiplyResult.outputBits)
      (q (guessFromProductRequest n instanceBits second state multiplyResult.outputBits).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult
    let returned := returnedFrameResult multiplySource multiplyRequest
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) saved multiplyResult
    let request := guessFromProductRequest n instanceBits second state multiplyResult.outputBits
    let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ multiplyResult.outputBits)
    let terminalBudget := completedGuessTerminalBudget q request multiplyRequest chooseRequest normalizeRequest body selected
      chooseResult normalizeResult multiplyResult
    (evalConfigWithin (completedGuessFromProductCompile guessSource) (returned.resumeAt 0)
      (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected multiplyResult.outputBits +
        (terminalBudget + 1))).map (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource request) (q request.length)).map
        (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  let original := encodeSecurityParameter n ++ frame instanceBits ++
    frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
  let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
    none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let back := storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult
  let returned := returnedFrameResult multiplySource multiplyRequest
    (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) saved multiplyResult
  let request := guessFromProductRequest n instanceBits second state multiplyResult.outputBits
  let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ multiplyResult.outputBits)
  let budget := completedGuessTerminalBudget q request multiplyRequest chooseRequest normalizeRequest body selected
    chooseResult normalizeResult multiplyResult
  have hLayout := returnedFrameResult_guessInput_layout multiplySource multiplyRequest
    (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back)
    before n instanceBits first second last reply message₀ message₁ state selected multiplyResult
  change returned.resumeAt 0 = _ at hLayout
  rw [hLayout]
  apply completedGuessFromProductCompile_evalResult guessSource before returned.outputTape.left
    n instanceBits first second last reply message₀ message₁ state selected multiplyResult.outputBits
    (2 * multiplyResult.outputTape.cells + 2 - multiplyResult.outputBits.length) q halts budget challenge
  intro c hc
  have hFits := completedGuessTerminalBudget_fits guessSource q request multiplyRequest chooseRequest normalizeRequest body selected
    chooseResult normalizeResult multiplyResult c hc
  have hNonempty : guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected multiplyResult.outputBits ≠ [] := by
    intro h
    have hLength := congrArg List.length h
    simp [guessFromProductSavedInput] at hLength
  cases hSaved : guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected multiplyResult.outputBits with
  | nil => exact False.elim (hNonempty hSaved)
  | cons boundary beforeInput =>
      have h := rawGuessResult_finishStoredGuess_eval_of_le multiplySource guessSource multiplyRequest request body selected
        beforeInput saved boundary back challenge multiplyResult c budget hFits
      simpa only [guessFromProductSavedOutput, hSaved, request, body, returned, back,
        storedGuessBackBlocks, List.length_cons, List.length_nil, List.cons_append] using h

/-- Every actual native branch of the complete post-product code halts
within the same budget used by its final-bit probability law. -/
theorem completedGuessFromProductCompile_returnedFrameResult_haltsFrom
    (multiplySource guessSource : Program) (q : Nat → Nat)
    (multiplyRequest chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (challenge : Bool) (chooseResult normalizeResult multiplyResult : Configuration)
    (halts : HaltsWithin guessSource
      (guessFromProductRequest n instanceBits second state multiplyResult.outputBits)
      (q (guessFromProductRequest n instanceBits second state multiplyResult.outputBits).length)) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let back := storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult
    let returned := returnedFrameResult multiplySource multiplyRequest
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) saved multiplyResult
    let request := guessFromProductRequest n instanceBits second state multiplyResult.outputBits
    let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ multiplyResult.outputBits)
    let terminalBudget := completedGuessTerminalBudget q request multiplyRequest chooseRequest normalizeRequest body selected
      chooseResult normalizeResult multiplyResult
    ∀ c, PaddedRunsFor (completedGuessFromProductCompile guessSource) (returned.resumeAt 0) c
      (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected multiplyResult.outputBits +
        (terminalBudget + 1)) → c.halted = true := by
  dsimp only
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _ (c.halted, c.outputBits)).mpr
    ⟨c, hc, rfl⟩
  rw [completedGuessFromProductCompile_returnedFrameResult_evalResult multiplySource guessSource q
    multiplyRequest chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state selected
    challenge chooseResult normalizeResult multiplyResult halts, PMF.mem_support_map_iff] at hm
  obtain ⟨d, _hd, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

/-- A coarse polynomial majorant for the complete post-product budget.
The source time is evaluated at the actual assembled guess request length;
no monotonicity or larger surrogate argument for `q` is assumed. -/
theorem completedGuessFromProductBudget_bound (q : Nat → Nat) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (multiplyRequest chooseRequest normalizeRequest : List Bool)
    (chooseResult normalizeResult multiplyResult : Configuration) :
    guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product +
      (completedGuessTerminalBudget q (guessFromProductRequest n instanceBits second state product)
        multiplyRequest chooseRequest normalizeRequest
        (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)) selected
        chooseResult normalizeResult multiplyResult + 1) ≤
      10000 * (n + instanceBits.length + first.length + second.length + last.length + reply.length +
        message₀.length + message₁.length + state.length + selected.length + product.length +
        multiplyRequest.length + chooseRequest.length + normalizeRequest.length +
        sourceStorage chooseResult + sourceStorage normalizeResult + sourceStorage multiplyResult + 1) *
        (q (guessFromProductRequest n instanceBits second state product).length + 1)^2 := by
  have h := guessFromProductBudget_bound q n instanceBits first second last reply message₀ message₁ state selected product
  have hLength : (guessFromProductRequest n instanceBits second state product).length =
      n + 2 * instanceBits.length + 4 * state.length + 4 * second.length + 2 * product.length + 9 := by
    simp [guessFromProductRequest, encodeSecurityParameter, frame, FiniteBitEncoding.delimit_length]
    omega
  have hPositive : 1 ≤ (q (guessFromProductRequest n instanceBits second state product).length + 1)^2 :=
    Nat.one_le_pow _ _ (by omega)
  have hQ : q (guessFromProductRequest n instanceBits second state product).length ≤
      (q (guessFromProductRequest n instanceBits second state product).length + 1)^2 := by nlinarith
  dsimp only [completedGuessTerminalBudget]
  simp only [List.length_cons, List.length_append, FiniteBitEncoding.delimit_length]
  rw [hLength] at h hPositive hQ ⊢
  nlinarith

/-- All-input stopping envelope for the complete guess continuation.
The terminal stage is charged on the actual storage grown by the preceding
randomized invocation, rather than on a freshly loaded reply. -/
def completedGuessRetainedBudget (coefficient degree storage : Nat) : Nat :=
  let invokeTime := guessRetainedBudget coefficient degree storage
  invokeTime + (4500000000 * (storage + invokeTime + 1) + 1)

theorem completedGuessRetainedBudget_polynomial (coefficient degree : Nat) :
    PolynomiallyBounded (completedGuessRetainedBudget coefficient degree) := by
  have hInvoke := guessRetainedBudget_polynomial coefficient degree
  have hStorage := (PolynomiallyBounded.id.add hInvoke).add (PolynomiallyBounded.const 1)
  exact hInvoke.add (((PolynomiallyBounded.const 4500000000).mul hStorage).add
    (PolynomiallyBounded.const 1))

theorem completedGuessRetainedBudget_monotone (coefficient degree : Nat) :
    Monotone (completedGuessRetainedBudget coefficient degree) := by
  intro first last h
  have hInvoke := guessRetainedBudget_monotone coefficient degree h
  have hStorage := Nat.add_le_add_right (Nat.add_le_add h hInvoke) 1
  exact Nat.add_le_add hInvoke
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4500000000 hStorage) 1)

/-- The complete native guess continuation stops on every branch from
arbitrary retained strings. The guessed reply need not be tagged correctly,
and the terminal processor receives exactly the tapes returned by the call.
Only the embedded source's all-input monomial stopping bound is assumed. -/
theorem completedGuessFromProductCompile_haltsFrom_retained_frontiers (source : Program)
    (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin source request (coefficient * (request.length + 1)^degree))
    (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∀ finish, PaddedRunsFor (completedGuessFromProductCompile source) start finish
      (completedGuessRetainedBudget coefficient degree (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
  let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
  let storage := sourceStorage start
  let invokeTime := guessRetainedBudget coefficient degree storage
  let terminalTime := 4500000000 * (storage + invokeTime + 1)
  have hFirst := guessFromProductCompile_haltsFrom_retained_frontiers source coefficient degree hSource
    before beforeOutput original reply canonical selected product inputBlanks outputBlanks
  have hSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin (guessFromProductCompile source) start invokeTime).support)
      (finish : Configuration)
      (run : PaddedRunsFor (finishStoredGuess 8 4) (c.resumeAt 0) finish terminalTime) :
      finish.halted = true := by
    have hStorage := sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    have hOutput : c.outputTape.cells ≤ storage + invokeTime := by
      dsimp only [sourceStorage] at hStorage
      change c.inputTape.cells + c.outputTape.cells ≤ storage + invokeTime at hStorage
      omega
    have hSmall : ∀ d, PaddedRunsFor (finishStoredGuess 8 4) (c.resumeAt 0) d
        (4500000000 * (c.outputTape.cells + 1)) → d.halted = true := by
      intro d hRun
      exact finishStoredGuess_haltsFrom_anyTape 8 4 c.inputTape c.outputTape d hRun
    have hBound : 4500000000 * (c.outputTape.cells + 1) ≤ terminalTime :=
      Nat.mul_le_mul_left 4500000000 (Nat.add_le_add_right hOutput 1)
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall] at hMem
    exact hSmall finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hLaw := Program.evalConfigWithin_twoStages_configuration (guessFromProductCompile source)
    (finishStoredGuess 8 4) start rfl rfl invokeTime terminalTime hFirst hSecond
  change evalConfigWithin (completedGuessFromProductCompile source) start
    (invokeTime + (terminalTime + 1)) = _ at hLaw
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  change finish ∈ (evalConfigWithin (completedGuessFromProductCompile source) start
    (invokeTime + (terminalTime + 1))).support at hMem
  rw [hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
  rw [PMF.mem_support_map_iff] at hFinish
  obtain ⟨target, _hTarget, rfl⟩ := hFinish
  rfl

/-- Apply the retained-string stopping certificate directly to the actual
framed multiplication return. The product is the called machine's raw output;
no correctness assumption or decoded group element is used for termination.
The returned source scratch remains on the output tape during the guess. -/
theorem completedGuessFromProductCompile_returnedFrameResult_haltsFrom_retained
    (multiplySource guessSource : Program) (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin guessSource request (coefficient * (request.length + 1)^degree))
    (multiplyRequest : List Bool) (beforeOutput before : List (Option Bool))
    (original reply canonical selected : List Bool) (multiplyResult : Configuration) :
    let saved := selected.reverse.map some ++ none :: canonical.reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := returnedFrameResult multiplySource multiplyRequest beforeOutput saved multiplyResult
    ∀ finish, PaddedRunsFor (completedGuessFromProductCompile guessSource) (returned.resumeAt 0) finish
      (completedGuessRetainedBudget coefficient degree (sourceStorage returned)) → finish.halted = true := by
  dsimp only
  let saved := selected.reverse.map some ++ none :: canonical.reverse.map some ++
    none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let returned := returnedFrameResult multiplySource multiplyRequest beforeOutput saved multiplyResult
  let start := restoreStoredInputStart
    (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
    canonical selected multiplyResult.outputBits none
    (List.replicate (2 * multiplyResult.outputTape.cells + 2 - multiplyResult.outputBits.length) none)
    { left := returned.outputTape.left }
  have hLayout : returned.resumeAt 0 = start := by
    simp [returned, returnedFrameResult, frameReturnedResultFinish, saved, start,
      restoreStoredInputStart, Configuration.resumeAt, List.append_assoc]
  have hStorage : sourceStorage returned = sourceStorage start := by
    have h := congrArg sourceStorage hLayout
    simpa only [sourceStorage, Configuration.resumeAt] using h
  have hStop := completedGuessFromProductCompile_haltsFrom_retained_frontiers guessSource
    coefficient degree hSource before returned.outputTape.left original reply canonical selected
    multiplyResult.outputBits (2 * multiplyResult.outputTape.cells + 2 - multiplyResult.outputBits.length) 0
  intro finish run
  change PaddedRunsFor (completedGuessFromProductCompile guessSource) (returned.resumeAt 0) finish
    (completedGuessRetainedBudget coefficient degree (sourceStorage returned)) at run
  rw [hLayout, hStorage] at run
  exact hStop finish run

private theorem cells_append_none_getD (cells : List (Option Bool)) (i : Nat) :
    cells.getD i none = (cells ++ [none]).getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- The complete guess continuation requires only three real retained
separators behind the framed product. A redundant outer blank gives the
existing four-block specification without altering any physical tape cell.
Malformed fields and arbitrary multiplication outputs are permitted. -/
theorem completedGuessFromProductCompile_returnedFrameResult_haltsFrom_separators
    (multiplySource guessSource : Program) (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin guessSource request (coefficient * (request.length + 1)^degree))
    (multiplyRequest : List Bool) (beforeOutput savedInput : List (Option Bool))
    (hSeparators : 3 ≤ savedInput.count none) (multiplyResult : Configuration) :
    let returned := returnedFrameResult multiplySource multiplyRequest beforeOutput savedInput multiplyResult
    ∀ finish, PaddedRunsFor (completedGuessFromProductCompile guessSource) (returned.resumeAt 0) finish
      (completedGuessRetainedBudget coefficient degree (sourceStorage returned + 1)) → finish.halted = true := by
  dsimp only
  let returned := returnedFrameResult multiplySource multiplyRequest beforeOutput savedInput multiplyResult
  let padded := returnedFrameResult multiplySource multiplyRequest beforeOutput (savedInput ++ [none]) multiplyResult
  obtain ⟨original, reply, canonical, selected, before, hSplit⟩ :=
    storedInput_four_blocks_of_separators savedInput hSeparators
  have hEquivalent : (returned.resumeAt 0).Equivalent (padded.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · refine ⟨rfl, ?_, fun _ => rfl⟩
      intro i
      change (multiplyResult.outputBits.reverse.map some ++ none :: savedInput).getD i none =
        (multiplyResult.outputBits.reverse.map some ++ none :: (savedInput ++ [none])).getD i none
      simpa only [List.append_assoc, List.cons_append] using
        cells_append_none_getD (multiplyResult.outputBits.reverse.map some ++ none :: savedInput) i
    · exact Tape.Equivalent.refl _
  have hStorage : sourceStorage padded = sourceStorage returned + 1 := by
    simp only [padded, returned, returnedFrameResult, frameReturnedResultFinish, sourceStorage,
      Tape.cells, List.length_append, List.length_cons, List.length_nil]
    omega
  have hStop := completedGuessFromProductCompile_returnedFrameResult_haltsFrom_retained
    multiplySource guessSource coefficient degree hSource multiplyRequest beforeOutput before
    original reply canonical selected multiplyResult
  change ∀ finish, PaddedRunsFor (completedGuessFromProductCompile guessSource)
    ((returnedFrameResult multiplySource multiplyRequest beforeOutput
      (selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
        none :: original.reverse.map some ++ none :: before) multiplyResult).resumeAt 0) finish
    (completedGuessRetainedBudget coefficient degree
      (sourceStorage (returnedFrameResult multiplySource multiplyRequest beforeOutput
        (selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
          none :: original.reverse.map some ++ none :: before) multiplyResult))) → finish.halted = true at hStop
  rw [← hSplit] at hStop
  change ∀ finish, PaddedRunsFor (completedGuessFromProductCompile guessSource) (padded.resumeAt 0) finish
    (completedGuessRetainedBudget coefficient degree (sourceStorage padded)) → finish.halted = true at hStop
  rw [hStorage] at hStop
  intro finish run
  have hMem : finish.halted ∈ ((evalConfigWithin (completedGuessFromProductCompile guessSource)
      (returned.resumeAt 0) (completedGuessRetainedBudget coefficient degree (sourceStorage returned + 1))).map
        Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ hEquivalent _ Configuration.halted
    (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hMem
  obtain ⟨target, hTarget, hEq⟩ := hMem
  exact hEq.symm.trans (hStop target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))

end Machine.GuardedCompiler
