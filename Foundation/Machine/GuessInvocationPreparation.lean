import Foundation.Machine.StoredGuessInvocation

namespace Machine.GuardedCompiler

/-- Assemble the complete guess request after multiplication, then invoke
the source adversary on those actual retained cells. The raw reply remains
on the physical input tape. Challenge retrieval, comparison and final output
cleanup are subsequent stages, not performed by this constructor. -/
def guessFromProductCompile (source : Program) : Program :=
  let pre := prepareGuessInput.asSubroutine 0 361
  Program.withSubroutine pre (storedGuessCallCompile source) [.halt]
    (pre.length + (storedGuessCallCompile source).length + 1)

def guessFromProductRequest (n : Nat) (instanceBits second state product : List Bool) : List Bool :=
  encodeSecurityParameter n ++ frame instanceBits ++
    frame (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product))

/-- Actual retained input cells beneath the returned raw guess. These are
shared with the subsequent native terminal stage, without a fresh load. -/
def guessFromProductSavedInput (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : List (Option Bool) :=
  let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: guessInputTupleTail first second last
  body.reverse.map some ++ none :: product.reverse.map some ++ none :: selected.reverse.map some ++
    none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
    none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before

/-- Actual retained output cells beneath the guarded guess invocation. -/
def guessFromProductSavedOutput (beforeOutput : List (Option Bool)) (state second product : List Bool) : List (Option Bool) :=
  none :: (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).reverse.map some ++ none :: beforeOutput

def guessFromProductBudget (q : Nat → Nat) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Nat :=
  prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product +
    (storedGuessCallTraceBudget q (guessFromProductRequest n instanceBits second state product) + 1)

private theorem guessFromProductEntry (before beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) (padding : Nat) :
    (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).resumeAt 0 =
      storedGuessCallStart (guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected product)
        (guessFromProductSavedOutput beforeOutput state second product)
        (guessFromProductRequest n instanceBits second state product)
        (padding - 1 - (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).length) :=
  prepareGuessInputFinish_call_layout before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding

/-- Full native invocation law from the post-multiplication tape layout.
The raw request, response and all source randomness come from actual machine
execution. Only observations invariant under redundant outer blank storage
are compared; no bits are supplied by a new initial-configuration operation. -/
theorem guessFromProductCompile_evalObservation {α : Type*} (source : Program)
    (before beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) (padding : Nat)
    (q : Nat → Nat)
    (halts : HaltsWithin source (guessFromProductRequest n instanceBits second state product)
      (q (guessFromProductRequest n instanceBits second state product).length))
    (observe : Configuration → α) (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (guessFromProductCompile source)
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product)).map observe =
      (evalConfigWithin source (preparedSource (guessFromProductRequest n instanceBits second state product))
        (q (guessFromProductRequest n instanceBits second state product).length)).map
          (fun c => observe { (rawResultFrom source (guessFromProductRequest n instanceBits second state product)
            (none :: guessFromProductSavedOutput beforeOutput state second product)
            (guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected product) c).swapTapes with
            pc := 361 + (storedGuessCallCompile source).length + 1, halted := true }) := by
  let pre := prepareGuessInput.asSubroutine 0 361
  let inputFinish := prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding
  let inputSteps := prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product
  let request := guessFromProductRequest n instanceBits second state product
  let savedInput := guessFromProductSavedInput before n instanceBits first second last reply message₀ message₁ state selected product
  let savedOutput := guessFromProductSavedOutput beforeOutput state second product
  let blanks := padding - 1 - (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).length
  let callStart := storedGuessCallStart savedInput savedOutput request blanks
  let callSteps := storedGuessCallTraceBudget q request
  let finalPc := 361 + (storedGuessCallCompile source).length + 1
  let final : Configuration → Configuration := fun c => { c with pc := finalPc, halted := true }
  have hPre : pre.length = 361 := by simp [pre, Program.asSubroutine_length, prepareGuessInput_length]
  have hRaw := prepareGuessInput_withSubroutine_eval []
    ((storedGuessCallCompile source).asSubroutine 361 finalPc ++ [.halt]) 361
    (by intro pc hpc; simp only [List.length_nil, Nat.zero_add, prepareGuessInput_length] at *; omega)
    before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding
  have hProgram : Program.withSubroutine [] prepareGuessInput
      ((storedGuessCallCompile source).asSubroutine 361 finalPc ++ [.halt]) 361 = guessFromProductCompile source := by
    simp only [guessFromProductCompile, Program.withSubroutine, Program.asSubroutine_length,
      prepareGuessInput_length, List.length_nil, List.nil_append, finalPc, List.append_assoc]
  rw [hProgram] at hRaw
  change evalReturnWithin (guessFromProductCompile source) 361
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    inputSteps = PMF.pure (inputFinish.resumeAt 361) at hRaw
  have hEntry : inputFinish.resumeAt 361 = callStart.rebasePc pre.length := by
    have h := congrArg (fun c : Configuration => c.rebasePc 361)
      (guessFromProductEntry before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    simpa [Configuration.resumeAt, Configuration.rebasePc, hPre, inputFinish,
      callStart, savedInput, savedOutput, request, blanks] using h
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (storedGuessCallCompile source) callStart
    (by change 0 ≤ (storedGuessCallCompile source).length; exact Nat.zero_le _) rfl callSteps
    (storedGuessCallCompile_haltsFrom source savedInput savedOutput request blanks q halts)
  dsimp only at hCall
  have hCaller : Program.withSubroutine pre (storedGuessCallCompile source) [.halt]
      (pre.length + (storedGuessCallCompile source).length + 1) = guessFromProductCompile source := rfl
  rw [hCaller, hPre] at hCall
  change evalConfigWithin (guessFromProductCompile source) (callStart.rebasePc 361)
    (callSteps + 1) = (evalConfigWithin (storedGuessCallCompile source) callStart callSteps).map final at hCall
  rw [hPre] at hEntry
  rw [← hEntry] at hCall
  have hTail (extra : Nat) :
      (evalConfigWithin (guessFromProductCompile source) (inputFinish.resumeAt 361)
        (callSteps + 1 + extra)).map observe =
      (evalConfigWithin (storedGuessCallCompile source) callStart callSteps).map (fun c => observe (final c)) := by
    have hStopped (c : Configuration) :
        evalConfigWithin (guessFromProductCompile source) (final c) extra = PMF.pure (final c) := by
      induction extra with
      | zero => rfl
      | succ extra ih =>
          rw [evalConfigWithin, ih, PMF.pure_bind]
          simp [stepPMF, next, final]
    rw [evalConfigWithin_add, hCall, PMF.bind_map, PMF.map_bind]
    simp only [Function.comp_def, hStopped, PMF.pure_map]
    rfl
  have hAfter := evalConfigWithin_after_return (guessFromProductCompile source) 361
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    inputSteps (callSteps + 1) observe (by
      intro d hd _hpc extra
      rw [hRaw] at hd
      have heq : d = inputFinish.resumeAt 361 := by simpa using hd
      subst d
      rw [hTail extra, hTail 0])
  change (evalConfigWithin (guessFromProductCompile source)
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    (inputSteps + (callSteps + 1))).map observe = _
  rw [hAfter, hRaw, PMF.pure_bind, hTail 0]
  exact storedGuessCallCompile_evalObservation source savedInput savedOutput request blanks q halts
    (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc finalPc).withHalted true))

theorem guessFromProductCompile_haltsFrom (source : Program)
    (before beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) (padding : Nat)
    (q : Nat → Nat)
    (halts : HaltsWithin source (guessFromProductRequest n instanceBits second state product)
      (q (guessFromProductRequest n instanceBits second state product).length))
    (finish : Configuration)
    (run : PaddedRunsFor (guessFromProductCompile source)
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      finish (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product)) :
    finish.halted = true := by
  have hm : finish.halted ∈
      ((evalConfigWithin (guessFromProductCompile source)
        (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
        (guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [guessFromProductCompile_evalObservation source before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding q halts
    Configuration.halted (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hm
  obtain ⟨c, _hc, heq⟩ := hm
  exact heq.symm

theorem guessFromProductCompile_length (source : Program) :
    (guessFromProductCompile source).length = 68*source.length + 525 := by
  simp [guessFromProductCompile, Program.withSubroutine, Program.asSubroutine_length,
    prepareGuessInput_length, storedGuessCallCompile_length]
  omega

/-- The source budget is evaluated on the actual assembled guess request,
not on the DDH input length or on a larger invented argument. This requires
no monotonicity of the source's polynomial-time witness. -/
theorem guessFromProductBudget_bound (q : Nat → Nat) (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    guessFromProductBudget q n instanceBits first second last reply message₀ message₁ state selected product ≤
      3000*(n + instanceBits.length + first.length + second.length + last.length + reply.length +
        message₀.length + message₁.length + state.length + selected.length + product.length + 1)*
        (q (guessFromProductRequest n instanceBits second state product).length + 1)^2 := by
  have hPrepare := prepareGuessInput_steps_le n instanceBits first second last reply message₀ message₁ state selected product
  have hCall := storedGuessCallTraceBudget_bound q (guessFromProductRequest n instanceBits second state product)
  have hLength : (guessFromProductRequest n instanceBits second state product).length =
      n + 2*instanceBits.length + 4*state.length + 4*second.length + 2*product.length + 9 := by
    simp [guessFromProductRequest, encodeSecurityParameter, frame, FiniteBitEncoding.delimit_length]
    omega
  have hPositive : 1 ≤ (q (guessFromProductRequest n instanceBits second state product).length + 1)^2 :=
    Nat.one_le_pow _ _ (by omega)
  dsimp only [guessFromProductBudget]
  rw [hLength] at hCall hPositive ⊢
  nlinarith

end Machine.GuardedCompiler
