import Foundation.Machine.StoredCallPreparation
import Foundation.Machine.ReturnedResultInvocation

namespace Machine.GuardedCompiler

/-- Native preparation of the retained caller tapes, followed by the real
source invocation and result framing. No raw request or returned result is
supplied by a fresh initial-configuration operation inside this program. -/
def storedFramedCallCompile (source : Program) : Program :=
  let pre := prepareStoredCall.asSubroutine 0 31
  let call := returnedFrameCompile source
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

def storedFramedCallTraceBudget (q : Nat → Nat) (first second third fourth request : List Bool) : Nat :=
  prepareStoredCallSteps first second third fourth request + returnedFrameTraceBudget q request.length + 1

theorem storedFramedCallCompile_length (source : Program) :
    (storedFramedCallCompile source).length = 68*source.length + 223 := by
  simp [storedFramedCallCompile, Program.withSubroutine, returnedFrameCompile_length,
    Program.asSubroutine_length, show prepareStoredCall.length = 30 from rfl]
  omega

theorem storedFramedCallTraceBudget_bound (q : Nat → Nat)
    (first second third fourth request : List Bool) :
    storedFramedCallTraceBudget q first second third fourth request ≤
      225*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := by
  have hRaw := returnedFrameTraceBudget_bound q request.length
  have hPositive : 1 ≤ (q request.length + 1)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [storedFramedCallTraceBudget, prepareStoredCallSteps]
  nlinarith

private theorem prepared_framed_eval {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (returnedFrameCompile source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      (returnedFrameTraceBudget q request.length)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe (returnedFrameResult source request (none :: beforeOutput)
          (fourth.reverse.map some ++ none :: third.reverse.map some ++
            none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c)) := by
  rw [evalConfigWithin_map_eq_of_equivalent (returnedFrameCompile source) _ _
    (prepareStoredCall_call_layout beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
    (returnedFrameTraceBudget q request.length) observe hObserve]
  have h := congrArg (fun law : PMF Configuration => law.map observe)
    (returnedFrameCompile_eval source request (none :: beforeOutput)
      (fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) q halts)
  simpa only [List.cons_append, List.append_assoc, PMF.map_comp, Function.comp_def] using h

private theorem prepared_framed_halts (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (returnedFrameCompile source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      finish (returnedFrameTraceBudget q request.length)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (returnedFrameCompile source)
        ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
        (returnedFrameTraceBudget q request.length)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [prepared_framed_eval source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm

private theorem compiled_layout (source : Program) :
    Program.withSubroutine [] prepareStoredCall
      ((returnedFrameCompile source).asSubroutine 31 (31 + (returnedFrameCompile source).length + 1) ++ [.halt]) 31 =
      storedFramedCallCompile source := by
  simp [storedFramedCallCompile, Program.withSubroutine, Program.asSubroutine_length,
    show prepareStoredCall.length = 30 from rfl, List.append_assoc]

/-- Full native preparation, invocation, and framing probability law on the
actual retained tapes. The observation must depend on cells, not redundant
outer blank representation. All three stages consume their own steps. -/
theorem storedFramedCallCompile_evalObservation {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedFramedCallTraceBudget q first second third fourth request)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe {
          returnedFrameResult source request (none :: beforeOutput)
            (fourth.reverse.map some ++ none :: third.reverse.map some ++
              none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c
          with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }) := by
  let pre := prepareStoredCall.asSubroutine 0 31
  let start := (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0
  let final : Configuration → Configuration := fun c =>
    { c with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }
  have hPrepare := (prepareStoredCall_runs beforeInput beforeOutput first second third fourth request
      inputBlanks outputBlanks).evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareStoredCall
    ((returnedFrameCompile source).asSubroutine 31 (31 + (returnedFrameCompile source).length + 1) ++ [.halt]) 31
    (by change 0 < 30; decide) rfl rfl prepareStoredCall_control_closed prepareStoredCall_no_randomBit
  rw [compiled_layout] at hPrepare
  change evalConfigWithin (storedFramedCallCompile source)
    (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
    (prepareStoredCallSteps first second third fourth request) =
      PMF.pure ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (returnedFrameCompile source) start
    (by change 0 ≤ (returnedFrameCompile source).length; exact Nat.zero_le _) rfl
    (returnedFrameTraceBudget q request.length)
    (prepared_framed_halts source beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks q halts)
  change evalConfigWithin (storedFramedCallCompile source) (start.rebasePc pre.length)
    (returnedFrameTraceBudget q request.length + 1) =
      (evalConfigWithin (returnedFrameCompile source) start (returnedFrameTraceBudget q request.length)).map final at hCall
  have hEntry : start.rebasePc pre.length =
      (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31 := rfl
  rw [hEntry] at hCall
  have hRaw := prepared_framed_eval source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (31 + (returnedFrameCompile source).length + 1)).withHalted true))
  rw [storedFramedCallTraceBudget, Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind,
    hCall, PMF.map_comp]
  exact hRaw

theorem storedFramedCallCompile_haltsFrom (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      finish (storedFramedCallTraceBudget q first second third fourth request)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (storedFramedCallCompile source)
        (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
        (storedFramedCallTraceBudget q first second third fourth request)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [storedFramedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm

/-- A storage-based envelope for a native call prepared from arbitrary
retained fields. Preparation and result framing are charged in addition
to every possible branch of the called program. -/
def storedFramedCallRetainedBudget (coefficient degree storage : Nat) : Nat :=
  10000000 * (storage + 1) * (coefficient * (storage + 1)^degree + 1)^2

theorem storedFramedCallRetainedBudget_polynomiallyBounded (coefficient degree : Nat) :
    PolynomiallyBounded (storedFramedCallRetainedBudget coefficient degree) :=
  ((PolynomiallyBounded.const 10000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).mul
      ((((PolynomiallyBounded.const coefficient).mul
        ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow degree)).add
          (PolynomiallyBounded.const 1)).pow 2)

theorem storedFramedCallRetainedBudget_monotone (coefficient degree : Nat) :
    Monotone (storedFramedCallRetainedBudget coefficient degree) := by
  intro first last h
  have hBase := Nat.add_le_add_right h 1
  have hTime := Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hBase degree)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 10000000 hBase)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hTime 1) 2)

private theorem storedFramedCallRetainedBudget_covers (coefficient degree storage used : Nat)
    (request : List Bool) (hUsed : used ≤ 1000000 * storage + 1000000)
    (hRequest : request.length ≤ storage) :
    used + (returnedFrameTraceBudget (fun m => coefficient * (m + 1)^degree) request.length + 1) ≤
      storedFramedCallRetainedBudget coefficient degree storage := by
  let q := fun m => coefficient * (m + 1)^degree
  have hSourceTime : q request.length ≤ coefficient * (storage + 1)^degree :=
    Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hRequest 1) degree)
  have hTime := returnedFrameTraceBudget_bound q request.length
  have hTimeBound : returnedFrameTraceBudget q request.length ≤
      200 * (storage + 1) * (coefficient * (storage + 1)^degree + 1)^2 := by
    apply hTime.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 200 (by omega))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hSourceTime 1) 2)
  have hPositive : 1 ≤ (coefficient * (storage + 1)^degree + 1)^2 := Nat.one_le_pow _ _ (by omega)
  change used + (returnedFrameTraceBudget q request.length + 1) ≤ _
  dsimp only [storedFramedCallRetainedBudget]
  nlinarith

private theorem storedFramedCallCompile_evalObservation_of_preparation {α : Type*}
    (source : Program) (start prepared : Configuration) (used : Nat)
    (request : List Bool) (beforeInput savedInput : List (Option Bool))
    (hPc : start.pc = 0) (hActive : start.halted = false)
    (run : RunsFor prepareStoredCall start prepared used) (hHalted : prepared.halted = true)
    (hLayout : (prepared.resumeAt 0).Equivalent
      (packInputStart (none :: beforeInput) (none :: savedInput) request).swapTapes)
    (q : Nat → Nat) (hSource : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (storedFramedCallCompile source) start
      (used + (returnedFrameTraceBudget q request.length + 1))).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe { returnedFrameResult source request (none :: beforeInput) savedInput c
          with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }) := by
  have hPrepare := run.evalConfigWithin_eq_pure_of_no_randomBit prepareStoredCall_no_randomBit
  have hFirst := run.haltsFrom_of_no_randomBit hHalted prepareStoredCall_no_randomBit (Nat.le_refl used)
  have hCall := returnedFrameCompile_haltsFrom source request (none :: beforeInput) savedInput q hSource
  have hSecond (c : Configuration) (hc : c ∈ (evalConfigWithin prepareStoredCall start used).support)
      (d : Configuration) (trace : PaddedRunsFor (returnedFrameCompile source) (c.resumeAt 0) d
        (returnedFrameTraceBudget q request.length)) : d.halted = true := by
    rw [hPrepare, PMF.mem_support_pure_iff] at hc
    subst c
    have hMem : d.halted ∈ ((evalConfigWithin (returnedFrameCompile source)
        (prepared.resumeAt 0) (returnedFrameTraceBudget q request.length)).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [evalConfigWithin_map_eq_of_equivalent (returnedFrameCompile source) _ _ hLayout
      _ Configuration.halted (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hMem
    obtain ⟨target, hTarget, hEq⟩ := hMem
    exact hEq.symm.trans (hCall target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareStoredCall
    (returnedFrameCompile source) start hPc hActive used (returnedFrameTraceBudget q request.length)
    hFirst hSecond
  change evalConfigWithin (storedFramedCallCompile source) start
    (used + (returnedFrameTraceBudget q request.length + 1)) = _ at hLaw
  rw [hLaw, hPrepare, PMF.pure_bind, PMF.map_comp]
  simp only [Program.asSubroutine_length, show prepareStoredCall.length = 30 from rfl,
    Function.comp_def]
  rw [evalConfigWithin_map_eq_of_equivalent (returnedFrameCompile source) _ _ hLayout _
    (fun c => observe { c with pc := 31 + (returnedFrameCompile source).length + 1, halted := true })
    (fun c d h => hObserve _ _ ((h.withPc _).withHalted true))]
  rw [returnedFrameCompile_eval source request (none :: beforeInput) savedInput q hSource, PMF.map_comp]
  rfl

/-- Malformed retained fields are allowed. Four native input scans reach
fresh guarded storage, and the actual output rewind determines the called
request. The called program must halt on every bitstring; no DDH validity
or canonical-response premise is used. No tapes are reset between stages. -/
theorem storedFramedCallCompile_haltsFrom_retained_suffix
    (source : Program) (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin source request (coefficient * (request.length + 1)^degree))
    (input : Tape) (savedOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth : List Bool) (inputBlanks moves : Nat)
    (hCells : ∀ i, (input.current :: input.right).getD i none =
      ((first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate inputBlanks none).drop moves).getD i none) :
    let start : Configuration :=
      { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    ∀ finish, PaddedRunsFor (storedFramedCallCompile source) start finish
      (storedFramedCallRetainedBudget coefficient degree (sourceStorage start)) → finish.halted = true := by
  dsimp only
  let start : Configuration :=
    { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let storage := sourceStorage start
  let q := fun m => coefficient * (m + 1)^degree
  obtain ⟨prepared, used, request, beforeInput, savedInput, hUsed, run, hHalted,
    hLength, _hCount, _hPrefix, hLayout⟩ := prepareStoredCall_terminates_with_call_layout_of_retained_suffix
      input savedOutput outputBlanks first second third fourth inputBlanks moves hCells
  have hRequest : request.length ≤ storage := by
    simp only [storage, sourceStorage, start, Tape.cells] at *
    omega
  have hBound : used + (returnedFrameTraceBudget q request.length + 1) ≤
      storedFramedCallRetainedBudget coefficient degree storage := by
    change used ≤ 1000000 * storage + 1000000 at hUsed
    exact storedFramedCallRetainedBudget_covers coefficient degree storage used request hUsed hRequest
  have hLaw := storedFramedCallCompile_evalObservation_of_preparation source start prepared used
    request beforeInput savedInput rfl rfl run hHalted hLayout q (hSource request)
    Configuration.halted (fun _ _ h => h.2.1)
  have hSmall (finish : Configuration) (trace : PaddedRunsFor (storedFramedCallCompile source) start finish
      (used + (returnedFrameTraceBudget q request.length + 1))) : finish.halted = true := by
    have hMem : finish.halted ∈ ((evalConfigWithin (storedFramedCallCompile source) start
        (used + (returnedFrameTraceBudget q request.length + 1))).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [hLaw, PMF.mem_support_map_iff] at hMem
    obtain ⟨c, _hc, hEq⟩ := hMem
    exact hEq.symm
  intro finish trace
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall] at hMem
  exact hSmall finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)

/-- The actual native call exposes its request and retained caller prefixes
even on a suffix of malformed fields. This state law supports subsequent
native continuations. Prefix lengths are bounded by actual preparation
storage; outer blank equivalence is used only for mathematical observation. -/
theorem storedFramedCallCompile_evalObservation_of_retained_suffix {α : Type*}
    (source : Program) (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin source request (coefficient * (request.length + 1)^degree))
    (input : Tape) (savedOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth : List Bool) (inputBlanks moves : Nat)
    (hCells : ∀ i, (input.current :: input.right).getD i none =
      ((first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate inputBlanks none).drop moves).getD i none)
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    let start : Configuration :=
      { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
    ∃ (request : List Bool) (beforeInput savedInput : List (Option Bool)),
      request.length ≤ savedOutput.length ∧ 3 ≤ savedInput.count none ∧
      beforeInput.length + savedInput.length ≤ 1000001 * (sourceStorage start + 1) ∧
      (evalConfigWithin (storedFramedCallCompile source) start
        (storedFramedCallRetainedBudget coefficient degree (sourceStorage start))).map observe =
        (evalConfigWithin source (preparedSource request) (coefficient * (request.length + 1)^degree)).map
          (fun c => observe { returnedFrameResult source request (none :: beforeInput) savedInput c
            with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }) := by
  dsimp only
  let start : Configuration :=
    { inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } }
  let storage := sourceStorage start
  let q := fun m => coefficient * (m + 1)^degree
  obtain ⟨prepared, used, request, beforeInput, savedInput, hUsed, run, hHalted,
    hLength, hCount, hPrefix, hLayout⟩ := prepareStoredCall_terminates_with_call_layout_of_retained_suffix
      input savedOutput outputBlanks first second third fourth inputBlanks moves hCells
  have hRequest : request.length ≤ storage := by
    simp only [storage, sourceStorage, start, Tape.cells] at *
    omega
  have hPrefixBound : beforeInput.length + savedInput.length ≤ 1000001 * (storage + 1) := by
    change used ≤ 1000000 * storage + 1000000 at hUsed
    change beforeInput.length + savedInput.length ≤ storage + used at hPrefix
    omega
  have hBound := storedFramedCallRetainedBudget_covers coefficient degree storage used request hUsed hRequest
  have hHaltLaw := storedFramedCallCompile_evalObservation_of_preparation source start prepared used
    request beforeInput savedInput rfl rfl run hHalted hLayout q (hSource request)
    Configuration.halted (fun _ _ h => h.2.1)
  have hSmall (finish : Configuration) (trace : PaddedRunsFor (storedFramedCallCompile source) start finish
      (used + (returnedFrameTraceBudget q request.length + 1))) : finish.halted = true := by
    have hMem : finish.halted ∈ ((evalConfigWithin (storedFramedCallCompile source) start
        (used + (returnedFrameTraceBudget q request.length + 1))).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [hHaltLaw, PMF.mem_support_map_iff] at hMem
    obtain ⟨c, _hc, hEq⟩ := hMem
    exact hEq.symm
  refine ⟨request, beforeInput, savedInput, hLength, hCount, hPrefixBound, ?_⟩
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall]
  exact storedFramedCallCompile_evalObservation_of_preparation source start prepared used
    request beforeInput savedInput rfl rfl run hHalted hLayout q (hSource request) observe hObserve

/-- If the called program returns one canonical result, its frame really
occupies these physical output cells after the whole charged invocation.
Reading cells here is a mathematical observation, not a machine copy opcode.
The full state law above remains available for a native continuation. -/
theorem storedFramedCallCompile_evalFrameCells (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request expected : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (correct : evalWithin source request (q request.length) = PMF.pure (some expected)) :
    (evalConfigWithin (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedFramedCallTraceBudget q first second third fourth request)).map
        (fun c => (c.halted, fun i : Fin (frame expected).length => c.outputTape.left.getD i.val none)) =
      PMF.pure (true, fun i : Fin (frame expected).length =>
        ((frame expected).reverse.map some).getD i.val none) := by
  let observe : Configuration → Bool × (Fin (frame expected).length → Option Bool) := fun c =>
    (c.halted, fun i => c.outputTape.left.getD i.val none)
  have hObserve : ∀ c d, c.Equivalent d → observe c = observe d := by
    intro c d h
    exact congrArg₂ Prod.mk h.2.1 (funext fun i => h.2.2.2.2.1 i.val)
  rw [storedFramedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts observe hObserve]
  have hOutput := (preparedSource_evalOutput source request (q request.length)).trans correct
  let target := (true, fun i : Fin (frame expected).length => ((frame expected).reverse.map some).getD i.val none)
  change (evalConfigWithin source (preparedSource request) (q request.length)).bind _ = PMF.pure target
  calc
    _ = (evalConfigWithin source (preparedSource request) (q request.length)).bind (fun _ => PMF.pure target) := by
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext c hc
      have hHalted := preparedSource_all_branches_halted source request _ halts c
        ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
      have hMem : (if c.halted then some c.outputBits else none) ∈
          ((evalConfigWithin source (preparedSource request) (q request.length)).map
            (fun d => if d.halted then some d.outputBits else none)).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨c, hc, rfl⟩
      rw [hOutput, PMF.mem_support_pure_iff] at hMem
      have hBits : c.outputBits = expected := by simpa only [hHalted, ↓reduceIte, Option.some.injEq] using hMem
      dsimp only [Function.comp_def]
      apply congrArg PMF.pure
      apply Prod.ext
      · rfl
      · funext i
        dsimp only [returnedFrameResult, frameReturnedResultFinish, target]
        rw [hBits]
        exact List.getD_append _ _ _ _ (by simp only [List.length_map, List.length_reverse]; exact i.isLt)
    _ = _ := PMF.bind_const _ _

end Machine.GuardedCompiler
