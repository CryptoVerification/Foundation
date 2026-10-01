import Foundation.Machine.NormalizationPreparation
import Foundation.Machine.OppositeCall

namespace Machine.GuardedCompiler

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> rfl
  | cons cell rest ih => cases i with
      | zero => rfl
      | succ i => exact ih i

private theorem getD_blank_padding (count i : Nat) :
    (List.replicate count (none : Option Bool)).getD i none = none := by
  induction count generalizing i with
  | zero => simp
  | succ count ih => cases i with
      | zero => simp [List.replicate_succ]
      | succ i => simp [List.replicate_succ]

private theorem rewound_normalization_equivalent (before : List (Option Bool)) (bits : List Bool) :
    (({ left := before, right := bits.map some ++ [none] } : Tape).moveRight).Equivalent
      { Tape.ofBits bits with left := none :: before } := by
  cases bits with
  | nil => exact Tape.Equivalent.refl _
  | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      exact getD_append_blank (rest.map some) i

/-- Native preparation reaches the ordinary guarded-call cell layout on
opposite physical tapes. Explicit trailing blanks remain in the actual
configuration; equivalence is proved cell by cell and is not a reset step. -/
theorem prepareChooseNormalization_call_layout (savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) :
    ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0).Equivalent
      (packInputStart (none :: savedOutput)
        (none :: (reply.reverse.map some ++ none ::
          ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none])))
        (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)).swapTapes := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    exact getD_blank_padding (blanks - 1) i
  · exact rewound_normalization_equivalent _ _


/-- Full returned-state law for any observation of physical tape cells.
The certificate is called on the prepared input; only redundant blank
representations may differ. This supports further native continuations,
whose head positions and protected prefixes cannot be recovered from a
concatenated output-bit observation alone. -/
theorem prepareChooseNormalization_call_evalObservation {α : Type*} (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (rawCompileOpposite normalizer)
      ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0)
      (rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map observe =
      (evalConfigWithin normalizer
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
        (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
        (fun c => observe ((rawResultFrom normalizer
          (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) (none :: savedOutput)
          (none :: (reply.reverse.map some ++ none ::
            ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none])))
          c).swapTapes)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
      (prepareChooseNormalization_call_layout savedOutput n instanceBits bit tupleTail reply blanks)
      _ observe hObserve,
    rawCompileOpposite_configuration_eval _ _ _ _ q halts, PMF.map_comp]
  rfl

/-- Invoke the given normalizer on the actual prepared finite input. Its
execution budget is evaluated at its own input length. No monotonicity of
that budget, and no free materialization of the raw source response, is used. -/
theorem prepareChooseNormalization_call_eval (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)) :
    (evalConfigWithin (rawCompileOpposite normalizer)
      ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0)
      (rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
      (fun c => (c.halted, c.inputTape.bits)) =
      (evalConfigWithin normalizer
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
        (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
        (fun c => (true, encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail) ++
          reply ++ c.outputBits)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
      (prepareChooseNormalization_call_layout savedOutput n instanceBits bit tupleTail reply blanks) _
      (fun c => (c.halted, c.inputTape.bits))
      (fun _ _ h => congrArg₂ Prod.mk h.2.1 h.2.2.1.bits),
    rawCompileOpposite_configuration_eval _ _ _ _ q halts, PMF.map_comp]
  apply congrArg (fun f => (evalConfigWithin normalizer
    (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
    (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map f)
  funext c
  change (true, ((rawResultFrom normalizer
    (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) (none :: savedOutput)
    (none :: (reply.reverse.map some ++ none ::
      ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none]))) c).swapTapes).inputTape.bits) = _
  rw [rawCompileOpposite_result_bits]
  simp [List.reverse_append, List.filterMap_append, List.append_assoc]

theorem prepareChooseNormalization_call_haltsFrom (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (finish : Configuration)
    (run : PaddedRunsFor (rawCompileOpposite normalizer)
      ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0)
      finish (rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)) :
    finish.halted = true := by
  have hMem : (finish.halted, finish.inputTape.bits) ∈
      ((evalConfigWithin (rawCompileOpposite normalizer)
        ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0)
        (rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
        (fun c => (c.halted, c.inputTape.bits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [prepareChooseNormalization_call_eval normalizer savedOutput n instanceBits bit tupleTail reply blanks q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact (congrArg Prod.fst hEq).symm

/-- Fixed finite native continuation from a returned choose source branch:
charged normalization-input preparation, guarded normalizer call, and halt.
The normalizer code is supplied once when constructing this syntax. -/
def normalizeChooseCompile (normalizer : Program) : Program :=
  let pre := prepareChooseNormalization.asSubroutine 0 95
  let call := rawCompileOpposite normalizer
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

def normalizationTraceBudget (q : Nat → Nat) (n : Nat)
    (instanceBits tuple reply : List Bool) : Nat :=
  prepareChooseNormalizationSteps n instanceBits tuple reply +
    rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length + 1

theorem normalizeChooseCompile_length (normalizer : Program) :
    (normalizeChooseCompile normalizer).length = 68 * normalizer.length + 252 := by
  simp [normalizeChooseCompile, Program.withSubroutine, Program.asSubroutine_length,
    rawCompileOpposite_length, show prepareChooseNormalization.length = 94 from rfl]
  omega

private theorem normalizeChooseCompile_layout (normalizer : Program) :
    normalizeChooseCompile normalizer =
      Program.withSubroutine [] prepareChooseNormalization
        ((rawCompileOpposite normalizer).asSubroutine 95
          (95 + (rawCompileOpposite normalizer).length + 1) ++ [.halt]) 95 := by
  simp only [normalizeChooseCompile, Program.withSubroutine, Program.asSubroutine_length,
    show prepareChooseNormalization.length = 94 from rfl, List.length_nil,
    Nat.reduceAdd, List.nil_append, List.append_assoc]


/-- A global monomial for the supplied normalizer yields a polynomial
budget in the actual retained caller storage. The request is assembled by
native instructions before its length is used to charge the guarded call. -/
def normalizationRetainedBudget (coefficient degree storage : Nat) : Nat :=
  let prepareTime := 200000000 * storage + 200000000
  let requestLimit := storage + prepareTime
  prepareTime +
    125 * (requestLimit + 1) * (coefficient * (requestLimit + 1)^degree + 1)^2 + 1

theorem normalizationRetainedBudget_polynomial (coefficient degree : Nat) :
    PolynomiallyBounded (normalizationRetainedBudget coefficient degree) := by
  have hPrepare : PolynomiallyBounded (fun m => 200000000 * m + 200000000) :=
    ((PolynomiallyBounded.const 200000000).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 200000000)
  have hLimit := PolynomiallyBounded.id.add hPrepare
  have hBase := hLimit.add (PolynomiallyBounded.const 1)
  have hTime := (PolynomiallyBounded.const coefficient).mul (hBase.pow degree)
  exact (hPrepare.add (((PolynomiallyBounded.const 125).mul hBase).mul
    ((hTime.add (PolynomiallyBounded.const 1)).pow 2))).add (PolynomiallyBounded.const 1)

/-- All branches of native normalization stop on every finite returned
choose reply with its actual separator and saved caller cells. The reply
and retained DDH prefix may be malformed. The guarded normalizer itself is
required to stop on every bitstring, not just well-formed requests. -/
theorem normalizeChooseCompile_haltsFrom_retainedReply (normalizer : Program)
    (coefficient degree : Nat)
    (hNormalizer : ∀ input : List Bool,
      HaltsWithin normalizer input (coefficient * (input.length + 1)^degree))
    (beforeInput savedOutput : List (Option Bool)) (reply : List Bool)
    (inputBlanks outputBlanks : Nat) :
    let initial : Configuration :=
      { inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
        outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    ∀ finish, PaddedRunsFor (normalizeChooseCompile normalizer) initial finish
      (normalizationRetainedBudget coefficient degree (sourceStorage initial)) → finish.halted = true := by
  let initial : Configuration :=
    { inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
      outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let q := fun m => coefficient * (m + 1)^degree
  obtain ⟨prepared, used, sourceSaved, targetSaved, request,
    hUsed, hPrepareRun, hPrepareHalt, hLayout, hRequestLength⟩ :=
    prepareChooseNormalization_terminates_with_guarded_layout beforeInput savedOutput reply inputBlanks outputBlanks
  let pre := prepareChooseNormalization.asSubroutine 0 95
  let call := rawCompileOpposite normalizer
  let start := prepared.resumeAt 0
  let rawTime := rawTraceBudget q request.length
  have hNormalizerHalts : HaltsWithin normalizer request (q request.length) := hNormalizer request
  have hCallerHalts (finish : Configuration) (run : PaddedRunsFor call start finish rawTime) :
      finish.halted = true := by
    have hEval := evalConfigWithin_map_eq_of_equivalent call start
      (packInputStart sourceSaved targetSaved request).swapTapes hLayout rawTime
      Configuration.halted (fun _ _ h => h.2.1)
    have hMem : finish.halted ∈ ((evalConfigWithin call start rawTime).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hEval, PMF.mem_support_map_iff] at hMem
    obtain ⟨target, hTarget, hSame⟩ := hMem
    exact hSame.symm.trans (rawCompileOpposite_haltsFrom normalizer request sourceSaved targetSaved
      q hNormalizerHalts target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))
  have hPrepare := hPrepareRun.evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareChooseNormalization
    (call.asSubroutine 95 (95 + call.length + 1) ++ [.halt]) 95
    (by change 0 < 94; decide) rfl hPrepareHalt prepareChooseNormalization_control_closed
    prepareChooseNormalization_no_randomBit
  rw [← normalizeChooseCompile_layout] at hPrepare
  change evalConfigWithin (normalizeChooseCompile normalizer) initial used =
    PMF.pure (prepared.resumeAt 95) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre call start
    (by change 0 ≤ call.length; exact Nat.zero_le _) rfl rawTime hCallerHalts
  change evalConfigWithin (normalizeChooseCompile normalizer) (prepared.resumeAt 95) (rawTime + 1) =
    (evalConfigWithin call start rawTime).map
      (fun c => { c with pc := 95 + call.length + 1, halted := true }) at hCall
  have hSelected (finish : Configuration)
      (run : PaddedRunsFor (normalizeChooseCompile normalizer) initial finish (used + rawTime + 1)) :
      finish.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind, hCall,
      PMF.mem_support_map_iff] at hMem
    obtain ⟨target, _hTarget, rfl⟩ := hMem
    rfl
  let storage := sourceStorage initial
  let preparationLimit := 200000000 * storage + 200000000
  let limit := storage + preparationLimit
  have hPrepareTime : used ≤ preparationLimit := hUsed
  have hStorage := sourceStorage_le_of_run hPrepareRun
  have hLength : request.length ≤ limit := by
    change prepared.inputTape.cells + prepared.outputTape.cells ≤ storage + used at hStorage
    dsimp only [limit]
    omega
  have hTime : q request.length ≤ coefficient * (limit + 1)^degree :=
    Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 1) degree)
  have hRaw := rawTraceBudget_bound q request.length
  have hRawBound : rawTime ≤ 125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 :=
    hRaw.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 125 (Nat.add_le_add_right hLength 1))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hTime 1) 2))
  have hBound : used + rawTime + 1 ≤ normalizationRetainedBudget coefficient degree storage := by
    change used + rawTime + 1 ≤ preparationLimit +
      125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 + 1
    omega
  dsimp only
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSelected] at hMem
  exact hSelected finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)

/-- The same retained-reply bound applies to the actual physical return
when only redundant outer blank representations differ. This uses native
evaluation's cell-equivalence law, without resetting either tape. -/
theorem normalizeChooseCompile_haltsFrom_equivalent_retainedReply (normalizer : Program)
    (coefficient degree : Nat)
    (hNormalizer : ∀ input : List Bool,
      HaltsWithin normalizer input (coefficient * (input.length + 1)^degree))
    (beforeInput savedOutput : List (Option Bool)) (reply : List Bool)
    (inputBlanks outputBlanks : Nat) (start : Configuration) :
    let initial : Configuration :=
      { inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
        outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    start.Equivalent initial → ∀ finish,
      PaddedRunsFor (normalizeChooseCompile normalizer) start finish
        (normalizationRetainedBudget coefficient degree (sourceStorage initial)) → finish.halted = true := by
  dsimp only
  intro hLayout finish run
  let initial : Configuration :=
    { inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
      outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let budget := normalizationRetainedBudget coefficient degree (sourceStorage initial)
  have hEval := evalConfigWithin_map_eq_of_equivalent (normalizeChooseCompile normalizer) start _ hLayout
    budget Configuration.halted (fun _ _ h => h.2.1)
  have hMem : finish.halted ∈
      ((evalConfigWithin (normalizeChooseCompile normalizer) start
        budget).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [hEval, PMF.mem_support_map_iff] at hMem
  obtain ⟨target, hTarget, hSame⟩ := hMem
  exact hSame.symm.trans
    (normalizeChooseCompile_haltsFrom_retainedReply normalizer coefficient degree hNormalizer
      beforeInput savedOutput reply inputBlanks outputBlanks target
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))

/-- Whole normalization stage, retaining the complete cell-observation law
for the subsequent native message-selection and arithmetic preparation.
The normalizer's source scratch is included on the physical output tape. -/
theorem normalizeChooseCompile_evalObservation {α : Type*} (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (normalizeChooseCompile normalizer)
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      (normalizationTraceBudget q n instanceBits (bit :: tupleTail) reply)).map observe =
      (evalConfigWithin normalizer
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
        (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
        (fun c => observe {
          (rawResultFrom normalizer
            (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) (none :: savedOutput)
            (none :: (reply.reverse.map some ++ none ::
              ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none])))
            c).swapTapes with pc := 95 + (rawCompileOpposite normalizer).length + 1, halted := true }) := by
  let pre := prepareChooseNormalization.asSubroutine 0 95
  let normalizerInput := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let start := (prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 0
  let final : Configuration → Configuration := fun c =>
    { c with pc := 95 + (rawCompileOpposite normalizer).length + 1, halted := true }
  have hPrepare := (prepareChooseNormalization_runs savedOutput n instanceBits bit tupleTail reply blanks).evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareChooseNormalization
    ((rawCompileOpposite normalizer).asSubroutine 95 (95 + (rawCompileOpposite normalizer).length + 1) ++ [.halt]) 95
    (by change 0 < 94; decide) rfl rfl prepareChooseNormalization_control_closed
    prepareChooseNormalization_no_randomBit
  rw [← normalizeChooseCompile_layout] at hPrepare
  change evalConfigWithin (normalizeChooseCompile normalizer)
    (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
    (prepareChooseNormalizationSteps n instanceBits (bit :: tupleTail) reply) =
      PMF.pure ((prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 95) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (rawCompileOpposite normalizer) start
    (by change 0 ≤ (rawCompileOpposite normalizer).length; exact Nat.zero_le _) rfl
    (rawTraceBudget q normalizerInput.length)
    (prepareChooseNormalization_call_haltsFrom normalizer savedOutput n instanceBits bit tupleTail reply blanks q halts)
  change evalConfigWithin (normalizeChooseCompile normalizer) (start.rebasePc pre.length)
    (rawTraceBudget q normalizerInput.length + 1) =
      (evalConfigWithin (rawCompileOpposite normalizer) start (rawTraceBudget q normalizerInput.length)).map final at hCall
  have hEntry : start.rebasePc pre.length =
      (prepareChooseNormalizationFinish savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 95 := rfl
  rw [hEntry] at hCall
  have hRaw := prepareChooseNormalization_call_evalObservation normalizer savedOutput n
    instanceBits bit tupleTail reply blanks q halts (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (95 + (rawCompileOpposite normalizer).length + 1)).withHalted true))
  rw [normalizationTraceBudget, Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind,
    hCall, PMF.map_comp]
  exact hRaw

/-- Entire native normalization continuation. Preparation is executed by
this same finite code before the guarded call. The raw reply is not
interpreted or replaced until the supplied normalizer executes. -/
theorem normalizeChooseCompile_evalResult (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)) :
    (evalConfigWithin (normalizeChooseCompile normalizer)
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      (normalizationTraceBudget q n instanceBits (bit :: tupleTail) reply)).map
      (fun c => (c.halted, c.inputTape.bits)) =
    (evalConfigWithin normalizer
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
      (fun c => (true, encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail) ++
        reply ++ c.outputBits)) := by
  rw [normalizeChooseCompile_evalObservation normalizer savedOutput n instanceBits bit tupleTail reply blanks
    q halts (fun c => (c.halted, c.inputTape.bits))
    (fun _ _ h => congrArg₂ Prod.mk h.2.1 h.2.2.1.bits)]
  congr 1
  funext c
  change (true, ((rawResultFrom normalizer
    (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) (none :: savedOutput)
    (none :: (reply.reverse.map some ++ none ::
      ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none])))
    c).swapTapes).inputTape.bits) = _
  rw [rawCompileOpposite_result_bits]
  simp [List.reverse_append, List.filterMap_append, List.append_assoc]

theorem normalizeChooseCompile_haltsFrom (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length))
    (finish : Configuration)
    (run : PaddedRunsFor (normalizeChooseCompile normalizer)
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      finish (normalizationTraceBudget q n instanceBits (bit :: tupleTail) reply)) :
    finish.halted = true := by
  have hMem : (finish.halted, finish.inputTape.bits) ∈
      ((evalConfigWithin (normalizeChooseCompile normalizer)
        (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
        (normalizationTraceBudget q n instanceBits (bit :: tupleTail) reply)).map
        (fun c => (c.halted, c.inputTape.bits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [normalizeChooseCompile_evalResult normalizer savedOutput n instanceBits bit tupleTail reply blanks q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact (congrArg Prod.fst hEq).symm

/-- Ordinary raw output semantics of the normalizer are preserved by the
whole native continuation. Halting excludes the timeout branch explicitly. -/
theorem normalizeChooseCompile_evalOutput (normalizer : Program)
    (savedOutput : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) (q : Nat → Nat)
    (halts : HaltsWithin normalizer
      (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)) :
    (evalConfigWithin (normalizeChooseCompile normalizer)
      (prepareChooseNormalizationStart savedOutput n instanceBits bit tupleTail reply blanks)
      (normalizationTraceBudget q n instanceBits (bit :: tupleTail) reply)).map
      (fun c => (c.halted, c.inputTape.bits)) =
    (evalWithin normalizer (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).map
      (fun output => (true, encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail) ++
        reply ++ output.getD [])) := by
  rw [normalizeChooseCompile_evalResult normalizer savedOutput n instanceBits bit tupleTail reply blanks q halts,
    ← preparedSource_evalOutput, PMF.map_comp]
  change (evalConfigWithin normalizer
    (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
    (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).bind _ =
      (evalConfigWithin normalizer
        (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
        (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hHalted := preparedSource_all_branches_halted normalizer
    (encodeSecurityParameter n ++ frame instanceBits ++ frame reply) _ halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  simp only [Function.comp_def, hHalted, ↓reduceIte, Option.getD_some]

/-- A guarded choose result already has exactly the contextual physical
layout used by normalization preparation. This identifies a branch fixture;
it does not load the original DDH input or source reply for free. -/
theorem rawResultFrom_normalizationStart (source : Program) (sourceInput : List Bool)
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail : List Bool)
    (c : Configuration) :
    let saved := none :: (encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none]
    let returned := (rawResultFrom source sourceInput [none] saved c).swapTapes
    returned.resumeAt 0 = prepareChooseNormalizationStart returned.outputTape.left
      n instanceBits bit tupleTail c.outputBits (2 * c.outputTape.cells + 2 - c.outputBits.length) := by
  simp [rawResultFrom, extractOutputFinish, copyScratchFinish, Configuration.swapTapes,
    Configuration.resumeAt, prepareChooseNormalizationStart, Configuration.outputBits, List.append_assoc]

/-- Polynomial overhead for preparation and the guarded normalizer, using
its budget at the exact normalization-input length. Original DDH input and
raw response sizes are both charged. No budget monotonicity is assumed. -/
theorem normalizationTraceBudget_bound (q : Nat → Nat) (n : Nat)
    (instanceBits tuple reply : List Bool) :
    normalizationTraceBudget q n instanceBits tuple reply ≤
      350 * ((encodeSecurityParameter n ++ frame instanceBits ++ frame tuple).length + reply.length + 1) *
        (q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length + 1) ^ 2 := by
  let size := (encodeSecurityParameter n ++ frame instanceBits ++ frame tuple).length + reply.length + 1
  let calls := q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length
  have hPrep := prepareChooseNormalizationSteps_le n instanceBits tuple reply
  have hCall := rawTraceBudget_bound q (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length
  have hSize : (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length + 1 ≤ 2 * size := by
    simp [size, frame]
    omega
  have hSquare : 1 ≤ (calls + 1) ^ 2 := Nat.one_le_pow' 2 calls
  have hPositive : 1 ≤ size := by simp [size]
  calc
    normalizationTraceBudget q n instanceBits tuple reply ≤
        50 * size + 31 + 125 * ((encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length + 1) * (calls + 1) ^ 2 := by
      dsimp only [normalizationTraceBudget, calls, size] at *
      omega
    _ ≤ 50 * size + 31 + 125 * (2 * size) * (calls + 1) ^ 2 := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right ((calls + 1) ^ 2) (Nat.mul_le_mul_left 125 hSize)) _
    _ = 50 * size + 31 + 250 * size * (calls + 1) ^ 2 := by ring
    _ ≤ 350 * size * (calls + 1) ^ 2 := by
      have hScaled := Nat.mul_le_mul_left size hSquare
      nlinarith

end Machine.GuardedCompiler
