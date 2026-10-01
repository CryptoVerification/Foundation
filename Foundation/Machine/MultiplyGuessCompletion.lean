import Foundation.Machine.GuessCompletion
import Foundation.Machine.MultiplyCallPreparation
import Foundation.Machine.StoredFramedCall

namespace Machine.GuardedCompiler

/-- The actual framed multiplication call followed by the complete guess
continuation. Both callees are finite native code on the same caller tapes;
no product, reply, or challenge is loaded between these stages. -/
def multiplyThenGuessCompile (multiplySource guessSource : Program) : Program :=
  let multiply := storedFramedCallCompile multiplySource
  let pre := multiply.asSubroutine 0 (multiply.length + 1)
  let guess := completedGuessFromProductCompile guessSource
  Program.withSubroutine pre guess [.halt] (pre.length + guess.length + 1)

theorem multiplyThenGuessCompile_length (multiplySource guessSource : Program) :
    (multiplyThenGuessCompile multiplySource guessSource).length =
      68 * multiplySource.length + 68 * guessSource.length + 911 := by
  simp only [multiplyThenGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, storedFramedCallCompile_length,
    completedGuessFromProductCompile_length, List.length_cons, List.length_nil]
  omega

/-- Include the native restoration of the original DDH input and framing
of the final multiplication operand before the two actual program calls. -/
def operandsMultiplyGuessCompile (multiplySource guessSource : Program) : Program :=
  let pre := prepareMultiplyOperands.asSubroutine 0 (prepareMultiplyOperands.length + 1)
  let call := multiplyThenGuessCompile multiplySource guessSource
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

theorem operandsMultiplyGuessCompile_length (multiplySource guessSource : Program) :
    (operandsMultiplyGuessCompile multiplySource guessSource).length =
      68 * multiplySource.length + 68 * guessSource.length + 1027 := by
  simp only [operandsMultiplyGuessCompile, Program.withSubroutine, List.length_append,
    Program.asSubroutine_length, multiplyThenGuessCompile_length,
    show prepareMultiplyOperands.length = 113 from rfl, List.length_cons, List.length_nil]
  omega

private theorem multiply_saved_original (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last : List Bool) :
    last.reverse.map some ++ multiplyCallBeforeElement before n instanceBits first second last =
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)).reverse.map some ++
        none :: before := by
  simp [multiplyCallBeforeElement, frame, encodeSecurityParameter,
    List.reverse_append, List.map_append, List.append_assoc]

/-- Complete ordinary execution after operand construction. The intermediate
source configurations come from the real framed multiplication invocation.
The common continuation budget must cover each of those branches; its
probability law retains both calls' source randomness. In particular the
source time functions are evaluated at the actual request lengths. -/
theorem multiplyThenGuessCompile_evalResult
    (multiplySource guessSource : Program) (qMultiply qGuess : Nat → Nat)
    (chooseRequest normalizeRequest : List Bool)
    (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (challenge : Bool) (chooseResult normalizeResult : Configuration) (blanks tailBudget : Nat)
    (hMultiply : HaltsWithin multiplySource
      (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
      (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).length))
    (hGuess : ∀ c ∈ (evalConfigWithin multiplySource
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last))
        (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).length)).support,
      HaltsWithin guessSource (guessFromProductRequest n instanceBits second state c.outputBits)
        (qGuess (guessFromProductRequest n instanceBits second state c.outputBits).length))
    (hFits : ∀ c ∈ (evalConfigWithin multiplySource
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last))
        (qMultiply (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).length)).support,
      guessFromProductBudget qGuess n instanceBits first second last reply message₀ message₁ state selected c.outputBits +
        (completedGuessTerminalBudget qGuess (guessFromProductRequest n instanceBits second state c.outputBits)
          (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last) chooseRequest normalizeRequest
          (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ c.outputBits)) selected
          chooseResult normalizeResult c + 1) ≤ tailBudget) :
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
    let canonical := canonicalMessageBits message₀ message₁ state
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    (evalConfigWithin (multiplyThenGuessCompile multiplySource guessSource)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin multiplySource (preparedSource request) (qMultiply request.length)).bind
        (fun c => (evalConfigWithin guessSource
          (preparedSource (guessFromProductRequest n instanceBits second state c.outputBits))
          (qGuess (guessFromProductRequest n instanceBits second state c.outputBits).length)).map
            (fun d => (true, [taggedGuessValue d.outputBits == challenge]))) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let canonical := canonicalMessageBits message₀ message₁ state
  let back := storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult
  let savedOutput := some challenge :: savedOutputBlocks back
  let callBefore := multiplyCallBeforeElement before n instanceBits first second last
  let outputBefore := none :: selected.reverse.map some ++ none :: savedOutput
  let start := prepareStoredCallStart callBefore outputBefore last reply canonical selected request
    blanks (instanceBits.length + 1 - (2 * last.length + 1))
  let multiply := storedFramedCallCompile multiplySource
  let guess := completedGuessFromProductCompile guessSource
  let steps := storedFramedCallTraceBudget qMultiply last reply canonical selected request
  let sourceDist := evalConfigWithin multiplySource (preparedSource request) (qMultiply request.length)
  let stageDist := evalConfigWithin multiply start steps
  let saved := selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
    none :: last.reverse.map some ++ callBefore
  let returned := fun c => returnedFrameResult multiplySource request (none :: outputBefore) saved c
  let observe : Configuration → Bool × List Bool := fun c => (c.halted, c.outputBits)
  let continuation := fun c : Configuration =>
    (evalConfigWithin guess (c.resumeAt 0) tailBudget).map observe
  let expected := fun c : Configuration =>
    (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state c.outputBits))
      (qGuess (guessFromProductRequest n instanceBits second state c.outputBits).length)).map
        (fun d => (true, [taggedGuessValue d.outputBits == challenge]))
  have hSaved : saved = selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
      none :: (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)).reverse.map some ++ none :: before := by
    dsimp only [saved]
    rw [show selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
        none :: last.reverse.map some ++ callBefore =
        selected.reverse.map some ++ none :: canonical.reverse.map some ++ none :: reply.reverse.map some ++
        none :: (last.reverse.map some ++ callBefore) by simp [List.append_assoc]]
    rw [multiply_saved_original]
    simp only [List.append_assoc, List.cons_append]
  have hRaw (c : Configuration) (hc : c ∈ sourceDist.support) :
      continuation (returned c) = expected c := by
    have hNative := completedGuessFromProductCompile_returnedFrameResult_evalResult multiplySource guessSource qGuess
      request chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state selected
      challenge chooseResult normalizeResult c (hGuess c hc)
    have hHalts := completedGuessFromProductCompile_returnedFrameResult_haltsFrom multiplySource guessSource qGuess
      request chooseRequest normalizeRequest before n instanceBits first second last reply message₀ message₁ state selected
      challenge chooseResult normalizeResult c (hGuess c hc)
    dsimp only at hNative hHalts
    simp only [List.cons_append] at hNative hHalts
    dsimp only [continuation, returned, expected]
    rw [hSaved]
    simp only [outputBefore, savedOutput, back, canonical, List.cons_append]
    rw [evalConfigWithin_eq_of_le guess _ _ tailBudget (hFits c hc) hHalts]
    exact hNative
  have hObserve : ∀ c d, c.Equivalent d → continuation c = continuation d := by
    intro c d h
    apply evalConfigWithin_map_eq_of_equivalent
    · exact (h.withPc 0).withHalted false
    · intro c d h; exact congrArg₂ Prod.mk h.2.1 h.outputBits
  have hFuture := storedFramedCallCompile_evalObservation multiplySource callBefore outputBefore
    last reply canonical selected request blanks (instanceBits.length + 1 - (2 * last.length + 1))
    qMultiply hMultiply continuation hObserve
  have hBind := congrArg (fun distribution : PMF (PMF (Bool × List Bool)) => distribution.bind id) hFuture
  simp only [PMF.bind_map, Function.comp_def, id_eq] at hBind
  have hContinuation : stageDist.bind continuation = sourceDist.bind expected := by
    change stageDist.bind continuation = _ at hBind
    rw [hBind]
    change sourceDist.bind _ = sourceDist.bind _
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext c hc
    exact hRaw c hc
  have hSecond : ∀ c ∈ stageDist.support,
      ∀ d, PaddedRunsFor guess (c.resumeAt 0) d tailBudget → d.halted = true := by
    intro c hc d run
    have hm : observe d ∈ (stageDist.bind continuation).support := by
      rw [PMF.mem_support_bind_iff]
      refine ⟨c, hc, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hContinuation, PMF.mem_support_bind_iff] at hm
    obtain ⟨e, _he, hm⟩ := hm
    rw [PMF.mem_support_map_iff] at hm
    obtain ⟨f, _hf, heq⟩ := hm
    exact (congrArg Prod.fst heq).symm
  rw [prepareMultiplyOperandsFinish_call_layout]
  have h := Program.evalConfigWithin_twoStages multiply guess start rfl rfl steps tailBudget
    (storedFramedCallCompile_haltsFrom multiplySource callBefore outputBefore last reply canonical selected request
      blanks (instanceBits.length + 1 - (2 * last.length + 1)) qMultiply hMultiply) hSecond
  exact h.trans hContinuation

/-- One common continuation budget when multiplication returns the specified
product. Its source scratch storage is charged by the prepared request plus
the actual multiplication transition bound, even if its internal branches
have different tape representations. -/
def multiplyGuessTailBudget (qMultiply qGuess : Nat → Nat)
    (multiplyRequest chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (chooseResult normalizeResult : Configuration) : Nat :=
  let request := guessFromProductRequest n instanceBits second state product
  let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)
  guessFromProductBudget qGuess n instanceBits first second last reply message₀ message₁ state selected product +
    (20 * (request.length + multiplyRequest.length + chooseRequest.length + normalizeRequest.length +
      body.length + selected.length + sourceStorage chooseResult + sourceStorage normalizeResult +
      (2 * multiplyRequest.length + 2 + qMultiply multiplyRequest.length) +
      (2 * request.length + 2 + qGuess request.length) + 1) + 200 + 1)

private theorem multiplyGuessTailBudget_fits (multiplySource : Program) (qMultiply qGuess : Nat → Nat)
    (multiplyRequest chooseRequest normalizeRequest : List Bool) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (chooseResult normalizeResult c : Configuration)
    (hc : c ∈ (evalConfigWithin multiplySource (preparedSource multiplyRequest) (qMultiply multiplyRequest.length)).support)
    (hProduct : c.outputBits = product) :
    guessFromProductBudget qGuess n instanceBits first second last reply message₀ message₁ state selected c.outputBits +
      (completedGuessTerminalBudget qGuess (guessFromProductRequest n instanceBits second state c.outputBits)
        multiplyRequest chooseRequest normalizeRequest
        (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ c.outputBits)) selected
        chooseResult normalizeResult c + 1) ≤
      multiplyGuessTailBudget qMultiply qGuess multiplyRequest chooseRequest normalizeRequest n
        instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult := by
  have hStorage := sourceStorage_le_of_padded_run ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hInitial := preparedSource_sourceStorage_le multiplyRequest
  rw [hProduct]
  dsimp only [completedGuessTerminalBudget, multiplyGuessTailBudget]
  omega

private theorem source_output_eq (source : Program) (request product : List Bool) (steps : Nat)
    (halts : HaltsWithin source request steps)
    (correct : evalWithin source request steps = PMF.pure (some product))
    (c : Configuration) (hc : c ∈ (evalConfigWithin source (preparedSource request) steps).support) :
    c.outputBits = product := by
  have hHalted := preparedSource_all_branches_halted source request steps halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hMem := (PMF.mem_support_map_iff
    (fun d : Configuration => if d.halted then some d.outputBits else none) _
    (if c.halted then some c.outputBits else none)).mpr ⟨c, hc, rfl⟩
  rw [preparedSource_evalOutput, correct, PMF.mem_support_pure_iff] at hMem
  simpa only [hHalted, ↓reduceIte, Option.some.injEq] using hMem

/-- A certified multiplication algorithm discharges the branch-dependent
continuation-budget premise. The full native wrapper returns precisely the
source guess distribution for that product, after comparison with the saved
challenge. No abstract simulation certificate or free arithmetic opcode is
used: `correct` refers to execution of the supplied finite multiply code. -/
theorem multiplyThenGuessCompile_correct
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
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
    let canonical := canonicalMessageBits message₀ message₁ state
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
      instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
    (evalConfigWithin (multiplyThenGuessCompile multiplySource guessSource)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
    instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
  let sourceDist := evalConfigWithin multiplySource (preparedSource request) (qMultiply request.length)
  have hOutput : ∀ c ∈ sourceDist.support, c.outputBits = product :=
    source_output_eq multiplySource request product _ hMultiply correct
  have h := multiplyThenGuessCompile_evalResult multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
    before n instanceBits first second last reply message₀ message₁ state selected challenge chooseResult normalizeResult blanks tailBudget
    hMultiply (by intro c hc; simpa only [hOutput c hc] using hGuess)
    (by
      intro c hc
      exact multiplyGuessTailBudget_fits multiplySource qMultiply qGuess request chooseRequest normalizeRequest n
        instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult c hc (hOutput c hc))
  rw [h]
  change sourceDist.bind _ = _
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = sourceDist.bindOnSupport (fun _ _ =>
        (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
          (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
            (fun c => (true, [taggedGuessValue c.outputBits == challenge]))) := by
      congr 1
      funext c hc
      rw [hOutput c hc]
    _ = _ := by rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

/-- Worst-case halting of the same combined native code, with no existential
choice of a successful random branch. The correctness law's support contains
only halted single-bit configurations. -/
theorem multiplyThenGuessCompile_correct_haltsFrom
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
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
    let canonical := canonicalMessageBits message₀ message₁ state
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
      instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
    ∀ c, PaddedRunsFor (multiplyThenGuessCompile multiplySource guessSource)
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0) c
      (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1)) → c.halted = true := by
  dsimp only
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, hc, rfl⟩
  rw [multiplyThenGuessCompile_correct multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
    before n instanceBits first second last reply message₀ message₁ state selected product challenge chooseResult normalizeResult blanks
    hMultiply correct hGuess, PMF.mem_support_map_iff] at hm
  obtain ⟨d, _hd, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

/-- Native operand restoration/framing, multiplication, guess request,
source invocation and finalization in one charged code. The same retained
input/output tapes pass through every stage of this continuation. -/
theorem operandsMultiplyGuessCompile_correct
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
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
    let canonical := canonicalMessageBits message₀ message₁ state
    let savedOutput := some challenge :: savedOutputBlocks
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
    let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
      instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
    (evalConfigWithin (operandsMultiplyGuessCompile multiplySource guessSource)
      (prepareMultiplyOperandsStart before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected)
      (prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected +
        (storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1) + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin guessSource (preparedSource (guessFromProductRequest n instanceBits second state product))
        (qGuess (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last
  let canonical := canonicalMessageBits message₀ message₁ state
  let savedOutput := some challenge :: savedOutputBlocks
    (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult)
  let start := prepareMultiplyOperandsStart before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  let finish := prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  let t₁ := prepareMultiplyOperandsSteps n instanceBits first second last reply canonical selected
  let tailBudget := multiplyGuessTailBudget qMultiply qGuess request chooseRequest normalizeRequest n
    instanceBits first second last reply message₀ message₁ state selected product chooseResult normalizeResult
  let t₂ := storedFramedCallTraceBudget qMultiply last reply canonical selected request + (tailBudget + 1)
  have hFinish : evalConfigWithin prepareMultiplyOperands start t₁ = PMF.pure finish :=
    prepareMultiplyOperands_eval _ _ _ _ _ _ _ _ _ _ _
  have hFirst : ∀ c, PaddedRunsFor prepareMultiplyOperands start c t₁ → c.halted = true := by
    intro c run
    have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [hFinish, PMF.mem_support_pure_iff] at hc
    subst c
    rfl
  have hSecond : ∀ c ∈ (evalConfigWithin prepareMultiplyOperands start t₁).support,
      ∀ d, PaddedRunsFor (multiplyThenGuessCompile multiplySource guessSource) (c.resumeAt 0) d t₂ → d.halted = true := by
    intro c hc
    rw [hFinish, PMF.mem_support_pure_iff] at hc
    subst c
    exact multiplyThenGuessCompile_correct_haltsFrom multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
      before n instanceBits first second last reply message₀ message₁ state selected product challenge chooseResult normalizeResult blanks
      hMultiply correct hGuess
  have h := Program.evalConfigWithin_twoStages prepareMultiplyOperands (multiplyThenGuessCompile multiplySource guessSource)
    start rfl rfl t₁ t₂ hFirst hSecond
  rw [hFinish, PMF.pure_bind] at h
  exact h.trans (multiplyThenGuessCompile_correct multiplySource guessSource qMultiply qGuess chooseRequest normalizeRequest
    before n instanceBits first second last reply message₀ message₁ state selected product challenge chooseResult normalizeResult blanks
    hMultiply correct hGuess)

end Machine.GuardedCompiler
