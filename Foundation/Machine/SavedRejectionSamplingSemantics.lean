import Foundation.Machine.RejectionSamplingSemantics

namespace Machine.RejectionSampling.Saved

open Foundation.Probability
open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    (evalConfigWithin program c steps).map report = PMF.pure (some c.outputBits) := by
  have same : evalConfigWithin program c steps = PMF.pure c := by
    induction steps with
    | zero => rfl
    | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]
  simp [same, PMF.pure_map, report, h]

private theorem eval_trialResult (before : List (Option Bool)) (modulus : List Bool)
    (bits : Fin modulus.length → Bool) (steps : Nat) :
    (evalConfigWithin program (trialResult before modulus bits) steps).map report =
      if Binary.value (List.ofFn bits) < Binary.value modulus then
        PMF.pure (some (List.ofFn bits))
      else (evalConfigWithin program (trialStart before modulus (List.ofFn bits)) steps).map report := by
  by_cases h : Binary.value (List.ofFn bits) < Binary.value modulus
  · rw [if_pos h, eval_halted _ _ (by simp [trialResult_halted, h]), trialResult_output]
  · rw [if_neg h]
    exact (trialResult_retry_equivalent before modulus bits h).evalOutput program steps

/-- The original q=1 guard, validation, and native rewind preserve the
protected caller prefix. This is the actual sampler entry at pc zero. -/
theorem eval_prepare (before : List (Option Bool)) (leading : List Bool) (hLeading : leading ≠ []) :
    let bits := leading ++ [true]
    evalConfigWithin program (initial before bits) (preparationSteps bits) =
      PMF.pure (validatedTrialStart before bits) := by
  dsimp only
  have guard : evalConfigWithin program (initial before (leading++[true]))
      (if (leading++[true]).headD false then 5 else 1) =
      PMF.pure (validationStart before (leading++[true])) := by
    cases leading with
    | nil => exact (hLeading rfl).elim
    | cons bit rest =>
      cases bit with
      | false => simpa using eval_guard_false before (rest++[true])
      | true =>
        cases rest with
        | nil => simpa using eval_guard_true before true []
        | cons bit rest => simpa using eval_guard_true before bit (rest++[true])
  rw [preparationSteps, evalConfigWithin_add, guard, PMF.pure_bind, eval_validateBody]

/-- Preserving a saved caller prefix leaves the exact retry weights
unchanged for every finite number of actual trials, including all rejected
branches and their charged physical head restoration. -/
theorem eval_trials (before : List (Option Bool)) (modulus previous : List Bool) (trials : Nat)
    (hPrevious : previous.length ≤ modulus.length) :
    (evalConfigWithin program (trialStart before modulus previous)
      (trials*(10*modulus.length+7))).map
        (fun c => if c.halted then some c.outputBits else none) = trialWeights modulus trials := by
  change (evalConfigWithin program (trialStart before modulus previous)
    (trials*(10*modulus.length+7))).map report = _
  induction trials generalizing previous with
  | zero => simp [evalConfigWithin, trialStart, trialWeights, PMF.pure_map, report]
  | succ trials ih =>
    have budget : (trials+1)*(10*modulus.length+7) =
        (10*modulus.length+7)+trials*(10*modulus.length+7) := by simp [Nat.add_mul, Nat.add_comm]
    rw [budget, evalConfigWithin_add, eval_trial before modulus previous hPrevious,
      PMF.map_bind, PMF.bind_map]
    simp only [Function.comp_def, eval_trialResult]
    conv_rhs => rw [trialWeights, candidateTrial, PMF.bind_map]
    congr 1
    funext bits
    simp only [Function.comp_def]
    split_ifs with h
    · rfl
    · exact ih (List.ofFn bits) (by simp)

/-- Preparation plus any finite number of retry blocks has the same exact
weights as the standalone sampler. The width counter remains on the physical
input tape throughout validation and every retry. -/
theorem eval_prepared_trials (before : List (Option Bool)) (leading : List Bool)
    (hLeading : leading ≠ []) (trials : Nat) :
    let bits := leading ++ [true]
    (evalConfigWithin program (initial before bits)
      (preparationSteps bits+trials*(10*bits.length+7))).map
        (fun c => if c.halted then some c.outputBits else none) = trialWeights bits trials := by
  dsimp only
  rw [evalConfigWithin_add, eval_prepare before leading hLeading, PMF.pure_bind]
  exact ((validatedTrialStart_equivalent before (leading++[true])).evalOutput program
    (trials*(10*(leading++[true]).length+7))).trans
      (eval_trials before (leading++[true]) [] trials (by simp))

/-- The saved counter does not affect the geometric rejection probability. -/
theorem timeout_trials (before : List (Option Bool)) (modulus previous : List Bool) (trials : Nat)
    (hPrevious : previous.length ≤ modulus.length) :
    ((evalConfigWithin program (trialStart before modulus previous)
      (trials*(10*modulus.length+7))).map
        (fun c => if c.halted then some c.outputBits else none)) none =
      (candidateTrial modulus none)^trials := by
  rw [eval_trials before modulus previous trials hPrevious, trialWeights_none]

/-- At these charged inspection times the failure-to-return probability is
at most 2^(-trials) for every positive canonical modulus with at least two
bits, even when its public representation originally had a much larger width. -/
theorem timeout_prepared_trials_le_half (before : List (Option Bool)) (leading : List Bool)
    (hLeading : leading ≠ []) (trials : Nat) :
    ((evalConfigWithin program (initial before (leading++[true]))
      (preparationSteps (leading++[true])+trials*(10*(leading++[true]).length+7))).map
        (fun c => if c.halted then some c.outputBits else none)) none ≤ (2⁻¹ : ℝ≥0∞)^trials := by
  rw [eval_prepared_trials before leading hLeading trials, trialWeights_none]
  simpa only [one_div] using pow_le_pow_left' (candidateTrial_none_le_half leading) trials

/-- Every accepted candidate in the exact first-trial law has a charged
native branch from the sampler's real entry. The physical saved prefix and
the end-of-block head positions are retained for the padding continuation. -/
theorem runs_first_trial (before : List (Option Bool)) (leading : List Bool)
    (hLeading : leading ≠ []) (draw : Fin (leading++[true]).length → Bool)
    (hAccepted : Binary.value (List.ofFn draw) < Binary.value (leading++[true])) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ preparationSteps (leading++[true])+10*(leading++[true]).length+7 ∧
      RunsFor program (initial before (leading++[true])) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (leading++[true]).reverse.map some ++ none::before } ∧
      target.outputTape.Equivalent { left := (List.ofFn draw).reverse.map some } := by
  have prepMember : validatedTrialStart before (leading++[true]) ∈
      (evalConfigWithin program (initial before (leading++[true])) (preparationSteps (leading++[true]))).support := by
    rw [eval_prepare before leading hLeading]
    simp
  obtain ⟨u, hu, prepRun⟩ := ((mem_support_evalConfigWithin_iff _ _ _ _).mp prepMember).toRunsFor_le
  have sampleMember : trialResult before (leading++[true]) draw ∈
      (evalConfigWithin program (trialStart before (leading++[true]) [])
        (10*(leading++[true]).length+7)).support := by
    rw [eval_trial before (leading++[true]) [] (by simp)]
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨draw, PMF.mem_support_uniformOfFintype draw, rfl⟩
  obtain ⟨v, hv, sampleRun⟩ := ((mem_support_evalConfigWithin_iff _ _ _ _).mp sampleMember).toRunsFor_le
  obtain ⟨target, actualRun, hActual⟩ := sampleRun.exists_equivalent
    (validatedTrialStart_equivalent before (leading++[true])).symm
  have halted : (trialResult before (leading++[true]) draw).halted = true := by
    rw [trialResult_halted, if_pos hAccepted]
  have input := trialResult_accepted_input before (leading++[true]) draw hAccepted
  have output := trialResult_accepted_output before (leading++[true]) draw hAccepted
  refine ⟨target, u+v, by omega, prepRun.trans actualRun, hActual.2.1.symm.trans halted, ?_, ?_⟩
  · simpa only [input] using hActual.2.2.1.symm
  · simpa only [output] using hActual.2.2.2.symm

/-- Actual expected transition count from the sampler entry with a protected
caller prefix. The prefix is physical tape data, not part of a reloaded input. -/
noncomputable def expectedTransitions (before : List (Option Bool)) (modulus : List Bool) : ℝ≥0∞ :=
  ∑' steps : Nat, ((evalConfigWithin program (initial before modulus) steps).map report) none

private theorem reported_some_monotone (start : Configuration) (bits : List Bool) :
    Monotone (fun steps => ((evalConfigWithin program start steps).map report) (some bits)) := by
  classical
  apply monotone_nat_of_le_succ
  intro steps
  rw [evalConfigWithin, PMF.map_apply, PMF.map_bind, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  by_cases h : some bits = report c
  · have hc : c.halted = true := by
      cases hh : c.halted <;> simp_all [report]
    have hs : stepPMF program c = PMF.pure c := by simp [stepPMF, next, hc]
    rw [hs, PMF.pure_map]
    simp [h]
  · simp [h]

private theorem reported_mass (start : Configuration) (steps : Nat) :
    (∑' bits, ((evalConfigWithin program start steps).map report) (some bits)) +
      ((evalConfigWithin program start steps).map report) none = 1 := by
  have h := (Equiv.optionEquivSumPUnit.{0, 0} (List Bool)).symm.tsum_eq
    (fun value => ((evalConfigWithin program start steps).map report) value)
  have h' := h.trans (PMF.tsum_coe _)
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at h'
  simpa using h'

private theorem reported_timeout_antitone (start : Configuration) :
    Antitone (fun steps => ((evalConfigWithin program start steps).map report) none) := by
  have hMass (steps : Nat) : ((evalConfigWithin program start steps).map report) none =
      1 - ∑' bits, ((evalConfigWithin program start steps).map report) (some bits) := by
    apply ENNReal.eq_sub_of_add_eq
    · exact ne_of_lt ((le_add_right le_rfl).trans_lt
        (by rw [reported_mass]; simp))
    · simpa [add_comm] using reported_mass start steps
  intro i j hij
  dsimp only
  rw [hMass i, hMass j]
  exact tsub_le_tsub_left
    (ENNReal.tsum_le_tsum (fun bits => reported_some_monotone start bits hij)) 1

/-- Exact rejection sampling retains its linear expected transition bound
with an arbitrary protected caller prefix. The bound uses the canonical
modulus length, rather than the public representation width. -/
theorem expectedTransitions_canonical (before : List (Option Bool))
    (leading : List Bool) (hLeading : leading ≠ []) :
    let bits := leading ++ [true]
    expectedTransitions before bits ≤ (24 * (bits.length + 1) : Nat) := by
  dsimp only
  let bits := leading ++ [true]
  let preparation := preparationSteps bits
  let block := 10 * bits.length + 7
  have hBlock : NeZero block := ⟨by dsimp [block]; omega⟩
  let timeout := fun steps => ((evalConfigWithin program (initial before bits) steps).map report) none
  have hEach (steps : Nat) : timeout (steps + preparation) ≤ (2⁻¹ : ℝ≥0∞) ^ (steps / block) := by
    exact (reported_timeout_antitone (initial before bits) (by
      have := Nat.div_mul_le_self steps block
      omega : preparation + (steps / block) * block ≤ steps + preparation)).trans
        (timeout_prepared_trials_le_half before leading hLeading (steps / block))
  have hTail : (∑' steps : Nat, timeout (steps + preparation)) ≤ (block : ℝ≥0∞) * 2 := by
    calc
      _ ≤ ∑' steps : Nat, (2⁻¹ : ℝ≥0∞) ^ (steps / block) := ENNReal.tsum_le_tsum hEach
      _ = ∑' pair : Nat × Fin block, (2⁻¹ : ℝ≥0∞) ^ pair.1 := by
        simpa using (Nat.divModEquiv block).tsum_eq
          (fun pair : Nat × Fin block => (2⁻¹ : ℝ≥0∞) ^ pair.1)
      _ = _ := by
        rw [ENNReal.tsum_prod']
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        norm_num
  have hExpected : expectedTransitions before bits ≤ (preparation : ℝ≥0∞) + (block : ℝ≥0∞) * 2 := by
    unfold expectedTransitions
    change (∑' steps : Nat, timeout steps) ≤ _
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := preparation)]
    apply add_le_add _ hTail
    calc
      _ ≤ ∑ _steps ∈ Finset.range preparation, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun steps _ => PMF.coe_le_one _ _)
      _ = _ := by simp
  apply hExpected.trans
  have hPrep : preparation ≤ 4 * bits.length + 10 := by
    dsimp [preparation, preparationSteps]
    split_ifs <;> omega
  calc
    _ ≤ ((4 * bits.length + 10 + 2 * block : Nat) : ℝ≥0∞) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      exact add_le_add (by exact_mod_cast hPrep) (by rw [mul_comm])
    _ ≤ ((24 * (bits.length + 1) : Nat) : ℝ≥0∞) := by
      exact_mod_cast (by dsimp [block]; omega :
        4 * bits.length + 10 + 2 * block ≤ 24 * (bits.length + 1))

/-- The contextual sampler halts with probability one; the limit concerns
real transitions from its entry configuration with the saved prefix. -/
theorem almostSureHalts_canonical (before : List (Option Bool))
    (leading : List Bool) (hLeading : leading ≠ []) :
    Filter.Tendsto
      (fun steps => ((evalConfigWithin program (initial before (leading++[true])) steps).map
        (fun c => if c.halted then some c.outputBits else none)) none)
      Filter.atTop (nhds 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  exact ne_of_lt ((expectedTransitions_canonical before leading hLeading).trans_lt
    (ENNReal.natCast_lt_top _))

/-- Unrenormalized eventual output mass for the actual contextual sampler. -/
noncomputable def eventualOutputMass (before : List (Option Bool))
    (modulus output : List Bool) : ℝ≥0∞ :=
  ⨆ steps : Nat, ((evalConfigWithin program (initial before modulus) steps).map report) (some output)

/-- Preserving physical caller data does not change any eventual output
probability. Together with almost-sure halting, this transfers the standalone
sampler's exact uniform law without renormalizing finite-budget timeouts. -/
theorem eventualOutputMass_eq (before : List (Option Bool))
    (leading : List Bool) (hLeading : leading ≠ []) (output : List Bool) :
    eventualOutputMass before (leading++[true]) output =
      Machine.outputMass program (leading++[true]) output := by
  let bits := leading ++ [true]
  let block := 10 * bits.length + 7
  have hSup : eventualOutputMass before bits output =
      ⨆ trials : Nat, ((evalConfigWithin program (initial before bits)
        (preparationSteps bits + trials * block)).map report) (some output) := by
    apply le_antisymm
    · apply iSup_le
      intro steps
      have hBound : steps ≤ preparationSteps bits + steps * block := by
        have h := Nat.le_mul_of_pos_right steps (by dsimp [block]; omega : 0 < block)
        omega
      exact (reported_some_monotone (initial before bits) output hBound).trans
        (le_iSup (fun trials => ((evalConfigWithin program (initial before bits)
          (preparationSteps bits + trials * block)).map report) (some output)) steps)
    · unfold eventualOutputMass
      exact iSup_le fun trials => le_iSup
        (fun steps => ((evalConfigWithin program (initial before bits) steps).map report) (some output))
        (preparationSteps bits + trials * block)
  rw [hSup]
  dsimp only [bits, block]
  change (⨆ trials : Nat, ((evalConfigWithin program (initial before (leading++[true]))
    (preparationSteps (leading++[true])+trials*(10*(leading++[true]).length+7))).map
      (fun c => if c.halted then some c.outputBits else none)) (some output)) = _
  simp_rw [eval_prepared_trials before leading hLeading, trialWeights_some]
  rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]
  exact (outputMass_geometric leading hLeading output).symm

/-- The contextual eventual law is exactly uniform on canonical residue
codes. This identifies each output probability of the actual saved-prefix
sampler, not a distribution conditioned on a successful finite trial. -/
theorem eventualOutputMass_uniform (before : List (Option Bool))
    (leading : List Bool) (hLeading : leading ≠ [])
    [Nonempty (Fin (Binary.value (leading++[true])))] (output : List Bool) :
    eventualOutputMass before (leading++[true]) output =
      ((uniform (Fin (Binary.value (leading++[true])))).map
        (fun a => Binary.encode (leading++[true]).length a.val)) output := by
  rw [eventualOutputMass_eq before leading hLeading output]
  exact congrArg (fun law : PMF (List Bool) => law output)
    (evalLimit_canonical leading hLeading)

end Machine.RejectionSampling.Saved
