import Foundation.Crypto.Semantics.Machine.DDHChooseCall

namespace Machine.GuardedCompiler

/-- Fixed native choose wrapper: read the actual DDH input, construct and
position the source choose request, invoke the guarded source on opposite
physical tapes, and halt. The source code is embedded syntactically. No
current key, instance, security parameter, or family is inserted in code.
This stage does not yet normalize the response or construct the challenge. -/
def chooseCompile (source : Program) : Program :=
  let pre := prepareDDHChooseCall.asSubroutine 0 119
  let call := rawCompileOpposite source
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

def chooseTraceBudget (q : Nat → Nat) (n : Nat) (instanceBits key tail : List Bool) : Nat :=
  prepareDDHChooseCallSteps n instanceBits key tail +
    rawTraceBudget q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length + 1

theorem chooseCompile_length (source : Program) :
    (chooseCompile source).length = 68 * source.length + 276 := by
  simp [chooseCompile, Program.withSubroutine, Program.asSubroutine_length,
    rawCompileOpposite_length, show prepareDDHChooseCall.length = 118 from rfl]
  omega

private theorem chooseCompile_layout (source : Program) :
    chooseCompile source =
      Program.withSubroutine [] prepareDDHChooseCall
        ((rawCompileOpposite source).asSubroutine 119
          (119 + (rawCompileOpposite source).length + 1) ++ [.halt]) 119 := by
  simp only [chooseCompile, Program.withSubroutine, Program.asSubroutine_length,
    show prepareDDHChooseCall.length = 118 from rfl, List.length_nil,
    Nat.reduceAdd, List.nil_append, List.append_assoc]

/-- Strengthened choose-stage law for any observation invariant under
redundant outer blank padding. Such observations may include the PMF of an
actual native continuation on both returned tapes. This retains the
protected source scratch state and all physical cell locations, rather
than reducing the result merely to its concatenated raw bits. -/
theorem chooseCompile_evalObservation {α : Type*} (source : Program) (n : Nat)
    (instanceBits key : List Bool) (nextBit : Bool) (tail : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (chooseCompile source)
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (chooseTraceBudget q n instanceBits key (nextBit :: tail))).map observe =
    (evalConfigWithin source
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map
      (fun c => observe {
        (rawResultFrom source
          (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)) [none]
          (none :: (encodeSecurityParameter n ++ frame instanceBits ++
            frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)).reverse.map some ++ [none]) c).swapTapes with
          pc := 119 + (rawCompileOpposite source).length + 1, halted := true }) := by
  let pre := prepareDDHChooseCall.asSubroutine 0 119
  let sourceInput := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)
  let start := (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)).resumeAt 0
  let final : Configuration → Configuration := fun c =>
    { c with pc := 119 + (rawCompileOpposite source).length + 1, halted := true }
  have hPrepare := (prepareDDHChooseCall_runs n instanceBits key nextBit tail).evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareDDHChooseCall
    ((rawCompileOpposite source).asSubroutine 119 (119 + (rawCompileOpposite source).length + 1) ++ [.halt]) 119
    (by change 0 < 118; decide) rfl rfl prepareDDHChooseCall_control_closed
    prepareDDHChooseCall_no_randomBit
  rw [← chooseCompile_layout] at hPrepare
  change evalConfigWithin (chooseCompile source)
    (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
    (prepareDDHChooseCallSteps n instanceBits key (nextBit :: tail)) =
      PMF.pure ((prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)).resumeAt 119) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (rawCompileOpposite source) start
    (by change 0 ≤ (rawCompileOpposite source).length; exact Nat.zero_le _) rfl
    (rawTraceBudget q sourceInput.length)
    (prepareDDHChooseCall_source_haltsFrom source n instanceBits key (nextBit :: tail) q halts)
  change evalConfigWithin (chooseCompile source) (start.rebasePc pre.length)
    (rawTraceBudget q sourceInput.length + 1) =
      (evalConfigWithin (rawCompileOpposite source) start (rawTraceBudget q sourceInput.length)).map final at hCall
  have hEntry : start.rebasePc pre.length =
      (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)).resumeAt 119 := rfl
  rw [hEntry] at hCall
  have hRaw := evalConfigWithin_map_eq_of_equivalent (rawCompileOpposite source) start _
    (prepareDDHChooseCall_source_layout n instanceBits key (nextBit :: tail))
    (rawTraceBudget q sourceInput.length) (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (119 + (rawCompileOpposite source).length + 1)).withHalted true))
  rw [rawCompileOpposite_configuration_eval _ _ _ _ q halts, PMF.map_comp] at hRaw
  rw [chooseTraceBudget, Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind,
    hCall, PMF.map_comp]
  exact hRaw

/-- Full choose invocation on actual finite DDH input. Preparation is part
of this same program and its charged execution budget. Both malformed and
well-formed source responses follow the original source distribution.
The physical input-tape observation retains the saved DDH tuple followed
by exactly the source response; the two tapes have not been reset for free. -/
theorem chooseCompile_evalResult (source : Program) (n : Nat)
    (instanceBits key : List Bool) (nextBit : Bool) (tail : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)) :
    (evalConfigWithin (chooseCompile source)
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (chooseTraceBudget q n instanceBits key (nextBit :: tail))).map
      (fun c => (c.halted, c.inputTape.bits)) =
    (evalConfigWithin source
      (preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map
      (fun c => (true, encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail) ++ c.outputBits)) := by
  rw [chooseCompile_evalObservation source n instanceBits key nextBit tail q halts
    (fun c => (c.halted, c.inputTape.bits))
    (fun _ _ h => congrArg₂ Prod.mk h.2.1 h.2.2.1.bits)]
  congr 1
  funext c
  change (true, ((rawResultFrom source
    (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)) [none]
    (none :: (encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)).reverse.map some ++ [none]) c).swapTapes).inputTape.bits) = _
  rw [rawCompileOpposite_result_bits]
  simp [List.reverse_append, List.filterMap_append, List.append_assoc]

/-- The complete native choose stage terminates on every source random
branch, with its preparation and final halt included in the displayed bound. -/
theorem chooseCompile_haltsWithin (source : Program) (n : Nat)
    (instanceBits key : List Bool) (nextBit : Bool) (tail : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)) :
    HaltsWithin (chooseCompile source)
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail))
      (chooseTraceBudget q n instanceBits key (nextBit :: tail)) := by
  intro finish run
  have hMem : (finish.halted, finish.inputTape.bits) ∈
      ((evalConfigWithin (chooseCompile source)
        (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
          frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
        (chooseTraceBudget q n instanceBits key (nextBit :: tail))).map
        (fun c => (c.halted, c.inputTape.bits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [chooseCompile_evalResult source n instanceBits key nextBit tail q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact (congrArg Prod.fst hEq).symm

/-- The choose stage's worst-case overhead is polynomial in the actual DDH
input length and the source time at its original choose-input length.
No monotonicity of the source budget is assumed or used. -/
theorem chooseTraceBudget_bound (q : Nat → Nat) (n : Nat) (instanceBits key tail : List Bool) :
    chooseTraceBudget q n instanceBits key tail ≤
      300 * ((encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ tail)).length + 1) *
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length + 1)^2 := by
  let m := (encodeSecurityParameter n ++ frame instanceBits ++ frame (FiniteBitEncoding.delimit key ++ tail)).length
  let k := (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length
  let t := (q k + 1)^2
  have hPrepare := prepareDDHChooseCallSteps_le n instanceBits key tail
  have hRaw := rawTraceBudget_bound q k
  have hInput : k ≤ m := by
    simp [k, m, encodeSecurityParameter, frame, FiniteBitEncoding.delimit_length]
    omega
  have hPositive : 1 ≤ t := by
    dsimp [t]
    exact Nat.one_le_pow _ _ (by omega)
  change chooseTraceBudget q n instanceBits key tail ≤ 300 * (m + 1) * t
  change prepareDDHChooseCallSteps n instanceBits key tail ≤ 60 * m + 100 at hPrepare
  change rawTraceBudget q k ≤ 125 * (k + 1) * t at hRaw
  dsimp only [chooseTraceBudget]
  change prepareDDHChooseCallSteps n instanceBits key tail + rawTraceBudget q k + 1 ≤ _
  nlinarith

/-- An all-input envelope for the complete native choose stage. The source
monomial is an analysis bound, not data embedded in the compiled program.
Malformed DDH inputs can generate malformed source requests; the source's
all-input termination hypothesis covers those requests too. -/
def chooseAllInputBudget (coefficient degree : Nat) (m : Nat) : Nat :=
  let sourceLimit := m + 2 + 20000000 * (m + 1)
  20000000 * (m + 1) +
    125 * (sourceLimit + 1) * (coefficient * (sourceLimit + 1)^degree + 1)^2 + 1

theorem chooseAllInputBudget_polynomial (coefficient degree : Nat) :
    PolynomiallyBounded (chooseAllInputBudget coefficient degree) := by
  have hPrepare : PolynomiallyBounded (fun m => 20000000 * (m + 1)) :=
    (PolynomiallyBounded.const 20000000).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
  have hLimit : PolynomiallyBounded (fun m => m + 2 + 20000000 * (m + 1)) :=
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)).add hPrepare
  have hBase := hLimit.add (PolynomiallyBounded.const 1)
  have hTime := (PolynomiallyBounded.const coefficient).mul (hBase.pow degree)
  exact (hPrepare.add (((PolynomiallyBounded.const 125).mul hBase).mul
    ((hTime.add (PolynomiallyBounded.const 1)).pow 2))).add (PolynomiallyBounded.const 1)

/-- Actual all-branch stopping on every raw input, including malformed
framed and delimited requests. Source execution uses fresh guarded regions
proved by the native preparation layout, without resetting caller tapes. -/
theorem chooseCompile_haltsWithin_anyInput (source : Program) (coefficient degree : Nat)
    (hSource : ∀ input : List Bool,
      HaltsWithin source input (coefficient * (input.length + 1)^degree))
    (input : List Bool) :
    HaltsWithin (chooseCompile source) input (chooseAllInputBudget coefficient degree input.length) := by
  let q := fun m => coefficient * (m + 1)^degree
  obtain ⟨prepared, used, beforeInput, beforeOutput, sourceInput,
    hUsed, hPrepareRun, hPrepareHalt, hLayout, hSourceLength⟩ :=
    prepareDDHChooseCall_terminates_with_layout input
  let pre := prepareDDHChooseCall.asSubroutine 0 119
  let call := rawCompileOpposite source
  let start := prepared.resumeAt 0
  let rawTime := rawTraceBudget q sourceInput.length
  have hSourceHalts : HaltsWithin source sourceInput (q sourceInput.length) := hSource sourceInput
  have hCallerHalts (finish : Configuration) (run : PaddedRunsFor call start finish rawTime) :
      finish.halted = true := by
    have hEval := evalConfigWithin_map_eq_of_equivalent call start
      (packInputStart beforeInput beforeOutput sourceInput).swapTapes hLayout rawTime
      Configuration.halted (fun _ _ h => h.2.1)
    have hMem : finish.halted ∈ ((evalConfigWithin call start rawTime).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hEval, PMF.mem_support_map_iff] at hMem
    obtain ⟨target, hTarget, hSame⟩ := hMem
    exact hSame.symm.trans (rawCompileOpposite_haltsFrom source sourceInput beforeInput beforeOutput
      q hSourceHalts target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))
  have hPrepare := hPrepareRun.evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareDDHChooseCall
    (call.asSubroutine 119 (119 + call.length + 1) ++ [.halt]) 119
    (by change 0 < 118; decide) rfl hPrepareHalt prepareDDHChooseCall_control_closed
    prepareDDHChooseCall_no_randomBit
  rw [← chooseCompile_layout] at hPrepare
  change evalConfigWithin (chooseCompile source) (Configuration.initial input) used =
    PMF.pure (prepared.resumeAt 119) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre call start
    (by change 0 ≤ call.length; exact Nat.zero_le _) rfl rawTime hCallerHalts
  change evalConfigWithin (chooseCompile source) (prepared.resumeAt 119) (rawTime + 1) =
    (evalConfigWithin call start rawTime).map
      (fun c => { c with pc := 119 + call.length + 1, halted := true }) at hCall
  have hSelected : HaltsWithin (chooseCompile source) input (used + rawTime + 1) := by
    intro finish run
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind, hCall,
      PMF.mem_support_map_iff] at hMem
    obtain ⟨target, _hTarget, rfl⟩ := hMem
    rfl
  apply hSelected.mono
  let limit := input.length + 2 + 20000000 * (input.length + 1)
  have hStorage := sourceStorage_le_of_run hPrepareRun
  simp only [sourceStorage] at hStorage
  have hInputCells : (Configuration.initial input).inputTape.cells ≤ input.length + 1 := by
    cases input with
    | nil => simp [Configuration.initial, Tape.ofBits, Tape.cells]
    | cons bit rest =>
        simp only [Configuration.initial, Tape.ofBits, Tape.cells, List.length_map, List.length_cons, List.length_nil]
        omega
  have hOutputCells : (Configuration.initial input).outputTape.cells = 1 := rfl
  have hLength : sourceInput.length ≤ limit := by dsimp only [limit]; omega
  have hTime : q sourceInput.length ≤ coefficient * (limit + 1)^degree :=
    Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 1) degree)
  have hRaw := rawTraceBudget_bound q sourceInput.length
  have hRawBound : rawTime ≤ 125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 :=
    hRaw.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 125 (Nat.add_le_add_right hLength 1))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hTime 1) 2))
  change used + rawTime + 1 ≤
    20000000 * (input.length + 1) +
      125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 + 1
  omega

private theorem chooseCompile_evalObservation_of_preparation {α : Type*}
    (source : Program) (start prepared : Configuration) (used : Nat)
    (request : List Bool) (sourceSaved targetSaved : List (Option Bool))
    (hPc : start.pc = 0) (hActive : start.halted = false)
    (run : RunsFor prepareDDHChooseCall start prepared used) (hHalted : prepared.halted = true)
    (hLayout : (prepared.resumeAt 0).Equivalent (packInputStart sourceSaved targetSaved request).swapTapes)
    (q : Nat → Nat) (hSource : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (chooseCompile source) start
      (used + (rawTraceBudget q request.length + 1))).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe {
          (rawResultFrom source request sourceSaved targetSaved c).swapTapes
          with pc := 119 + (rawCompileOpposite source).length + 1, halted := true }) := by
  have hPrepare := run.evalConfigWithin_eq_pure_of_no_randomBit prepareDDHChooseCall_no_randomBit
  have hFirst := run.haltsFrom_of_no_randomBit hHalted prepareDDHChooseCall_no_randomBit (Nat.le_refl used)
  have hCall := rawCompileOpposite_haltsFrom source request sourceSaved targetSaved q hSource
  have hSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareDDHChooseCall start used).support)
      (d : Configuration) (trace : PaddedRunsFor (rawCompileOpposite source) (c.resumeAt 0) d
        (rawTraceBudget q request.length)) : d.halted = true := by
    rw [hPrepare, PMF.mem_support_pure_iff] at hc
    subst c
    have hMem : d.halted ∈ ((evalConfigWithin (rawCompileOpposite source)
        (prepared.resumeAt 0) (rawTraceBudget q request.length)).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨d, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [evalConfigWithin_map_eq_of_equivalent (rawCompileOpposite source) _ _ hLayout _
      Configuration.halted (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hMem
    obtain ⟨target, hTarget, hEq⟩ := hMem
    exact hEq.symm.trans (hCall target ((mem_support_evalConfigWithin_iff _ _ _ _).mp hTarget))
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareDDHChooseCall
    (rawCompileOpposite source) start hPc hActive used (rawTraceBudget q request.length) hFirst hSecond
  change evalConfigWithin (chooseCompile source) start
    (used + (rawTraceBudget q request.length + 1)) = _ at hLaw
  rw [hLaw, hPrepare, PMF.pure_bind, PMF.map_comp]
  simp only [Program.asSubroutine_length, show prepareDDHChooseCall.length = 118 from rfl, Function.comp_def]
  rw [evalConfigWithin_map_eq_of_equivalent (rawCompileOpposite source) _ _ hLayout _
    (fun c => observe { c with pc := 119 + (rawCompileOpposite source).length + 1, halted := true })
    (fun c d h => hObserve _ _ ((h.withPc _).withHalted true))]
  rw [rawCompileOpposite_configuration_eval source request sourceSaved targetSaved q hSource, PMF.map_comp]
  rfl

/-- Complete cell-observation law on every finite DDH input. Native
preparation supplies the actual request and a protected blank separator.
Malformed requests are passed to the source unchanged; no validity parser
or newly loaded caller tape is used in this law. -/
theorem chooseCompile_evalObservation_anyInput {α : Type*} (source : Program)
    (q : Nat → Nat) (hSource : ∀ request : List Bool, HaltsWithin source request (q request.length))
    (input : List Bool) (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    ∃ (used : Nat) (sourceInput : List Bool) (beforeInput beforeOutput : List (Option Bool)),
      used ≤ 20000000 * (input.length + 1) ∧
      (evalConfigWithin (chooseCompile source) (Configuration.initial input)
        (used + rawTraceBudget q sourceInput.length + 1)).map observe =
      (evalConfigWithin source (preparedSource sourceInput) (q sourceInput.length)).map
        (fun c => observe {
          (rawResultFrom source sourceInput beforeInput (none :: beforeOutput) c).swapTapes with
          pc := 119 + (rawCompileOpposite source).length + 1, halted := true }) := by
  obtain ⟨prepared, used, beforeInput, beforeOutput, sourceInput,
    hUsed, hPrepareRun, hPrepareHalt, hLayout, _hSourceLength⟩ :=
    prepareDDHChooseCall_terminates_with_separated_layout input
  refine ⟨used, sourceInput, beforeInput, beforeOutput, hUsed, ?_⟩
  rw [Nat.add_assoc]
  exact chooseCompile_evalObservation_of_preparation source (Configuration.initial input) prepared used
    sourceInput beforeInput (none :: beforeOutput) rfl rfl hPrepareRun hPrepareHalt hLayout q
    (hSource sourceInput) observe hObserve

private theorem choose_prepared_size_bound (m used : Nat)
    (hUsed : used ≤ 20000000 * (m + 1)) :
    m + 3 + used ≤ 20000003 * (m + 1) := by omega

/-- All-input choose-call law at one polynomial input-length budget. The
saved prefixes are described by actual physical cells (with one redundant
outer blank when needed), so their lengths and the source request are
bounded by the charged preparation. No tape is reloaded or discarded. -/
theorem chooseCompile_evalObservation_anyInput_bounded {α : Type*}
    (source : Program) (coefficient degree : Nat)
    (hSource : ∀ request : List Bool,
      HaltsWithin source request (coefficient * (request.length + 1)^degree))
    (input : List Bool) (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    ∃ (request : List Bool) (sourceSaved targetSaved : List (Option Bool)),
      request.length ≤ 20000003 * (input.length + 1) ∧
      sourceSaved.length + (none :: targetSaved).length ≤ 20000003 * (input.length + 1) ∧
      (evalConfigWithin (chooseCompile source) (Configuration.initial input)
        (chooseAllInputBudget coefficient degree input.length)).map observe =
      (evalConfigWithin source (preparedSource request)
        (coefficient * (request.length + 1)^degree)).map
        (fun c => observe {
          (rawResultFrom source request sourceSaved (none :: targetSaved) c).swapTapes
          with pc := 119 + (rawCompileOpposite source).length + 1, halted := true }) := by
  let q := fun m => coefficient * (m + 1)^degree
  obtain ⟨prepared, used, _oldSource, _oldTarget, request, hUsed, run, hHalt, hLayout, hRequest⟩ :=
    prepareDDHChooseCall_terminates_with_separated_layout input
  have hLeft : ∀ i, prepared.inputTape.left.getD i none =
      (none :: prepared.inputTape.left.tail).getD i none := by
    intro i
    cases i with
    | zero =>
        have h := hLayout.2.2.1.2.1 0
        simpa only [Configuration.resumeAt, Configuration.swapTapes, packInputStart,
          List.getD_cons_zero] using h
    | succ i =>
        cases h : prepared.inputTape.left <;> simp
  have hPhysicalLayout : (prepared.resumeAt 0).Equivalent
      (packInputStart prepared.outputTape.left (none :: prepared.inputTape.left.tail) request).swapTapes := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact ⟨hLayout.2.2.1.1, hLeft, hLayout.2.2.1.2.2⟩
    · exact ⟨hLayout.2.2.2.1, fun _ => rfl, hLayout.2.2.2.2.2⟩
  have hStorage := sourceStorage_le_of_run run
  have hInitial : sourceStorage (Configuration.initial input) ≤ input.length + 2 := by
    cases input with
    | nil => simp [sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells]
    | cons bit rest =>
        simp [sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells]
        omega
  have hStorageBound := hStorage.trans (Nat.add_le_add_right hInitial used)
  have hLength : request.length ≤ input.length + 2 + used := by
    dsimp only [sourceStorage] at hStorageBound
    omega
  have hTail : prepared.inputTape.left.tail.length ≤ prepared.inputTape.left.length := by
    simp only [List.length_tail]
    exact Nat.sub_le _ _
  have hPrefix : prepared.outputTape.left.length + (none :: prepared.inputTape.left.tail).length ≤
      input.length + 3 + used := by
    dsimp only [sourceStorage, Tape.cells] at hStorageBound
    simp only [List.length_cons]
    omega
  have hMajor := choose_prepared_size_bound input.length used hUsed
  have hRequestBound : request.length ≤ 20000003 * (input.length + 1) :=
    hLength.trans ((Nat.add_le_add_right (Nat.add_le_add_left (by decide : 2 ≤ 3) input.length) used).trans hMajor)
  have hPrefixBound : prepared.outputTape.left.length + (none :: prepared.inputTape.left.tail).length ≤
      20000003 * (input.length + 1) := hPrefix.trans hMajor
  let limit := input.length + 2 + 20000000 * (input.length + 1)
  have hLimit : request.length ≤ limit := hLength.trans (Nat.add_le_add_left hUsed (input.length + 2))
  have hTime : q request.length ≤ coefficient * (limit + 1)^degree :=
    Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hLimit 1) degree)
  have hRaw := rawTraceBudget_bound q request.length
  have hRawBound : rawTraceBudget q request.length ≤
      125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 :=
    hRaw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 125 (Nat.add_le_add_right hLimit 1))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hTime 1) 2))
  have hCovers : used + (rawTraceBudget q request.length + 1) ≤
      chooseAllInputBudget coefficient degree input.length := by
    change _ ≤ 20000000 * (input.length + 1) +
      125 * (limit + 1) * (coefficient * (limit + 1)^degree + 1)^2 + 1
    simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add hUsed hRawBound) 1
  have hLaw := chooseCompile_evalObservation_of_preparation source (Configuration.initial input) prepared used
    request prepared.outputTape.left (none :: prepared.inputTape.left.tail) rfl rfl run hHalt hPhysicalLayout q
    (hSource request) observe hObserve
  have hHaltLaw := chooseCompile_evalObservation_of_preparation source (Configuration.initial input) prepared used
    request prepared.outputTape.left (none :: prepared.inputTape.left.tail) rfl rfl run hHalt hPhysicalLayout q
    (hSource request) Configuration.halted (fun _ _ h => h.2.1)
  have hSmall (finish : Configuration)
      (trace : PaddedRunsFor (chooseCompile source) (Configuration.initial input) finish
        (used + (rawTraceBudget q request.length + 1))) : finish.halted = true := by
    have hMem : finish.halted ∈ ((evalConfigWithin (chooseCompile source) (Configuration.initial input)
        (used + (rawTraceBudget q request.length + 1))).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [hHaltLaw, PMF.mem_support_map_iff] at hMem
    obtain ⟨target, _hTarget, hEq⟩ := hMem
    exact hEq.symm
  refine ⟨request, prepared.outputTape.left, prepared.inputTape.left.tail, hRequestBound, hPrefixBound, ?_⟩
  rw [evalConfigWithin_eq_of_le _ _ _ _ hCovers hSmall]
  exact hLaw

/-- A global source monomial gives a polynomial-time native choose wrapper.
The function and its stopping proof quantify over all finite bitstrings. -/
theorem chooseCompile_polynomialTime_of_monomial (source : Program) (coefficient degree : Nat)
    (hSource : ∀ input : List Bool,
      HaltsWithin source input (coefficient * (input.length + 1)^degree)) :
    PolynomialTime (chooseCompile source) :=
  ⟨chooseAllInputBudget coefficient degree, chooseAllInputBudget_polynomial coefficient degree,
    chooseCompile_haltsWithin_anyInput source coefficient degree hSource⟩

end Machine.GuardedCompiler
