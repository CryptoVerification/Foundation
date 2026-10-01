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

end Machine.GuardedCompiler
