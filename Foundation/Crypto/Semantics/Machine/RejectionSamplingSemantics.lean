import Foundation.Crypto.Semantics.Machine.RejectionSampling
import Foundation.Crypto.Semantics.Machine.RetryExpectation

namespace Machine.RejectionSampling

open Foundation.Probability
open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

/-- The finite one-trial law is proved from the original code below. This
mathematical PMF is not added as a machine instruction. -/
noncomputable def candidateTrial (modulus : List Bool) : PMF (Option (List Bool)) :=
  (uniform (Fin modulus.length → Bool)).map (fun bits =>
    if Binary.value (List.ofFn bits) < Binary.value modulus then some (List.ofFn bits) else none)

private theorem candidateTrial_number (modulus : List Bool) :
    candidateTrial modulus = (uniform (Fin (2 ^ modulus.length))).map (fun x =>
      if x.val < Binary.value modulus then some (Binary.encode modulus.length x.val) else none) := by
  unfold candidateTrial
  rw [← uniform_map_equiv (Binary.bitsEquiv modulus.length), PMF.map_comp]
  congr 1
  funext bits
  have hCode : Binary.encode modulus.length (Binary.value (List.ofFn bits)) = List.ofFn bits := by
    simpa only [List.length_ofFn] using Binary.encode_value (List.ofFn bits)
  simp only [Function.comp_def, Binary.bitsEquiv_val, hCode]

/-- Per-trial rejection probability, computed from the finite code's
uniform candidate law. -/
theorem candidateTrial_none (modulus : List Bool) :
    candidateTrial modulus none =
      ((2 ^ modulus.length - Binary.value modulus : Nat) : ℝ≥0∞) /
        (2 ^ modulus.length : Nat) := by
  classical
  let N := 2 ^ modulus.length
  let q := Binary.value modulus
  have hq : q ≤ N := (Binary.value_lt modulus).le
  let rejected : Set (Fin N) := {x | q ≤ x.val}
  let e : rejected ≃ Fin (N - q) :=
    { toFun := fun x => ⟨x.val.val - q, by have := x.val.isLt; have hx : q ≤ x.val.val := x.property; omega⟩
      invFun := fun x => ⟨⟨x.val + q, by have := x.isLt; omega⟩, by change q ≤ x.val + q; omega⟩
      left_inv := by intro x; apply Subtype.ext; apply Fin.ext; change x.val.val - q + q = x.val.val; have hx : q ≤ x.val.val := x.property; omega
      right_inv := by intro x; apply Fin.ext; change x.val + q - q = x.val; omega }
  have hCard : Fintype.card rejected = N - q :=
    (Fintype.card_congr e).trans (Fintype.card_fin _)
  rw [candidateTrial_number, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  have hSet : (fun x : Fin N => if x.val < q then
      some (Binary.encode modulus.length x.val) else none) ⁻¹' {none} = rejected := by
    ext x
    simp [rejected, not_lt]
  change (uniform (Fin N)).toOuterMeasure
    ((fun x : Fin N => if x.val < q then
      some (Binary.encode modulus.length x.val) else none) ⁻¹' {none}) = _
  rw [hSet]
  change (PMF.uniformOfFintype (Fin N)).toOuterMeasure rejected = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, hCard]
  simp [N, q, div_eq_mul_inv]

/-- Every canonical positive modulus accepts at least half of the fixed-width
candidates. This implementation uses the modulus bit length, including its
most-significant one, rather than a minimal candidate width. -/
theorem candidateTrial_none_le_half (leading : List Bool) :
    candidateTrial (leading ++ [true]) none ≤ (1 / 2 : ℝ≥0∞) := by
  let bits := leading ++ [true]
  let a := 2 ^ leading.length
  have hN : 2 ^ bits.length = 2 * a := by simp [bits, a, pow_succ, Nat.mul_comm]
  have hLower : a ≤ Binary.value bits := Binary.value_canonical_lower leading
  have hDifference : 2 ^ bits.length - Binary.value bits ≤ a := by omega
  have hNonzero : ((2 ^ bits.length : Nat) : ℝ≥0∞) ≠ 0 := by simp
  rw [candidateTrial_none, ENNReal.div_le_iff hNonzero (by simp)]
  calc
    _ ≤ (a : ℝ≥0∞) := by exact_mod_cast hDifference
    _ = (1 / 2 : ℝ≥0∞) * (2 ^ (leading ++ [true]).length : Nat) := by
      change _ = (1 / 2 : ℝ≥0∞) * (2 ^ bits.length : Nat)
      rw [hN, Nat.cast_mul, ← mul_assoc]
      simp [ENNReal.inv_mul_cancel]

/-- The positive candidate `a`'s code has the original uniform candidate
mass in one trial; rejection only discards candidates outside the modulus. -/
theorem candidateTrial_encoded (modulus : List Bool) (a : Fin (2 ^ modulus.length))
    (ha : a.val < Binary.value modulus) :
    candidateTrial modulus (some (Binary.encode modulus.length a.val)) =
      ((2 ^ modulus.length : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [candidateTrial_number, PMF.map_apply, tsum_eq_single a]
  · simp [ha, uniform]
  · intro x hxa
    by_cases hx : x.val < Binary.value modulus
    · have hCode : Binary.encode modulus.length x.val ≠ Binary.encode modulus.length a.val := by
        intro h
        have hv := congrArg Binary.value h
        rw [Binary.value_encode x.isLt, Binary.value_encode a.isLt] at hv
        exact hxa (Fin.ext hv)
      simp [hx, Ne.symm hCode]
    · simp [hx]

noncomputable def trialWeights (modulus : List Bool) : Nat → PMF (Option (List Bool))
  | 0 => PMF.pure none
  | trials + 1 => (candidateTrial modulus).bind (fun result =>
      match result with
      | none => trialWeights modulus trials
      | some _ => PMF.pure result)

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    (evalConfigWithin program c steps).map report = PMF.pure (some c.outputBits) := by
  have hEval : evalConfigWithin program c steps = PMF.pure c := by
    induction steps with
    | zero => rfl
    | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]
  simp [hEval, PMF.pure_map, report, h]

private theorem eval_trialResult (modulus : List Bool) (bits : Fin modulus.length → Bool)
    (steps : Nat) :
    (evalConfigWithin program (trialResult modulus bits) steps).map report =
      if Binary.value (List.ofFn bits) < Binary.value modulus then
        PMF.pure (some (List.ofFn bits))
      else (evalConfigWithin program (trialStart modulus (List.ofFn bits)) steps).map report := by
  by_cases h : Binary.value (List.ofFn bits) < Binary.value modulus
  · rw [if_pos h, eval_halted _ _ (by simp [trialResult_halted, h]), trialResult_output]
  · rw [if_neg h]
    exact (trialResult_retry_equivalent modulus bits h).evalOutput program steps

/-- Operational inspection after any number of complete trials agrees with
independent retry weights. Head restoration and rejected candidates remain
on the physical tapes, and are handled by cell equivalence. -/
theorem eval_trials (modulus previous : List Bool) (trials : Nat)
    (hPrevious : previous.length ≤ modulus.length) :
    (evalConfigWithin program (trialStart modulus previous)
      (trials * (10 * modulus.length + 7))).map
        (fun c => if c.halted then some c.outputBits else none) = trialWeights modulus trials := by
  change (evalConfigWithin program (trialStart modulus previous)
    (trials * (10 * modulus.length + 7))).map report = _
  induction trials generalizing previous with
  | zero => simp [evalConfigWithin, trialStart, trialWeights, PMF.pure_map, report]
  | succ trials ih =>
      have hBudget : (trials + 1) * (10 * modulus.length + 7) =
          (10 * modulus.length + 7) + trials * (10 * modulus.length + 7) := by simp [Nat.add_mul, Nat.add_comm]
      rw [hBudget, evalConfigWithin_add, eval_trial modulus previous hPrevious,
        PMF.map_bind, PMF.bind_map]
      simp only [Function.comp_def, eval_trialResult]
      conv_rhs => rw [trialWeights, candidateTrial, PMF.bind_map]
      congr 1
      funext bits
      simp only [Function.comp_def]
      split_ifs with h
      · rfl
      · exact ih (List.ofFn bits) (by simp)

/-- The probability of still waiting is a geometric power of the exact
one-trial rejection probability. -/
theorem trialWeights_none (modulus : List Bool) (trials : Nat) :
    trialWeights modulus trials none = (candidateTrial modulus none) ^ trials := by
  induction trials with
  | zero => simp [trialWeights]
  | succ trials ih =>
      rw [trialWeights, PMF.bind_apply, tsum_eq_single none]
      · simp [ih, pow_succ, mul_comm]
      · intro result hResult
        cases result with
        | none => exact (hResult rfl).elim
        | some bits => simp

/-- Each accepted code accumulates the geometric retry weights without any
renormalization of finite-budget nontermination. -/
theorem trialWeights_some (modulus bits : List Bool) (trials : Nat) :
    trialWeights modulus trials (some bits) =
      candidateTrial modulus (some bits) *
        ∑ i ∈ Finset.range trials, (candidateTrial modulus none) ^ i := by
  classical
  induction trials with
  | zero => simp [trialWeights]
  | succ trials ih =>
      rw [trialWeights, PMF.bind_apply, tsum_eq_sum (s := {none, some bits})]
      · simp only [Finset.sum_insert (by simp : none ∉ ({some bits} : Finset (Option (List Bool)))),
          Finset.sum_singleton, PMF.pure_apply, ih]
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Finset.mul_sum, pow_succ]
        simp only [ite_true, mul_one, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      · intro other hOther
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hOther
        cases other with
        | none => exact (hOther.1 rfl).elim
        | some xs => simp [PMF.pure_apply, Ne.symm hOther.2]

/-- Real validation and tape restoration, charged before the first trial. -/
def preparationSteps (modulus : List Bool) : Nat :=
  (if modulus.headD false then 5 else 1) + (4 * modulus.length + 5)

theorem eval_prepare (leading : List Bool) (hLeading : leading ≠ []) :
    let bits := leading ++ [true]
    evalConfigWithin program (Configuration.initial bits) (preparationSteps bits) =
      PMF.pure (validatedTrialStart bits) := by
  dsimp only
  have hGuard : evalConfigWithin program (Configuration.initial (leading ++ [true]))
      (if (leading ++ [true]).headD false then 5 else 1) =
      PMF.pure (validationStart (leading ++ [true])) := by
    cases leading with
    | nil => exact (hLeading rfl).elim
    | cons bit rest =>
        cases bit with
        | false => simpa using eval_guard_false (rest ++ [true])
        | true =>
            cases rest with
            | nil => simpa using eval_guard_true true []
            | cons bit rest => simpa using eval_guard_true bit (rest ++ [true])
  rw [preparationSteps, evalConfigWithin_add, hGuard, PMF.pure_bind, eval_validateBody]

theorem eval_prepared_trials (leading : List Bool) (hLeading : leading ≠ []) (trials : Nat) :
    let bits := leading ++ [true]
    evalWithin program bits (preparationSteps bits + trials * (10 * bits.length + 7)) =
      trialWeights bits trials := by
  dsimp only
  unfold evalWithin
  rw [evalConfigWithin_add, eval_prepare leading hLeading, PMF.pure_bind]
  have hEq := (validatedTrialStart_equivalent (leading ++ [true])).evalOutput program
    (trials * (10 * (leading ++ [true]).length + 7))
  change (evalConfigWithin program (validatedTrialStart (leading ++ [true])) _).map report = _
  change (evalConfigWithin program (validatedTrialStart (leading ++ [true])) _).map report =
    (evalConfigWithin program (trialStart (leading ++ [true]) []) _).map report at hEq
  rw [hEq]
  exact eval_trials (leading ++ [true]) [] trials (by simp)

theorem timeout_prepared_trials (leading : List Bool) (hLeading : leading ≠ []) (trials : Nat) :
    let bits := leading ++ [true]
    timeoutProbability program bits (preparationSteps bits + trials * (10 * bits.length + 7)) =
      (candidateTrial bits none) ^ trials := by
  dsimp only
  unfold timeoutProbability eventProb
  rw [eval_prepared_trials leading hLeading]
  change (trialWeights (leading ++ [true]) trials).toOuterMeasure {none} = _
  rw [PMF.toOuterMeasure_apply_singleton, trialWeights_none]

private theorem expectedSteps_canonical (leading : List Bool) (hLeading : leading ≠ []) :
    let bits := leading ++ [true]
    expectedSteps program bits ≤ (24 * (bits.length + 1) : Nat) := by
  dsimp only
  let bits := leading ++ [true]
  let block := 10 * bits.length + 7
  have hBlock : NeZero block := ⟨by dsimp [block]; omega⟩
  have h := expectedSteps_le_of_timeout_blocks_after (p := program) (input := bits)
    (preparationSteps bits) block (1 / 2) (fun trials => by
      rw [timeout_prepared_trials leading hLeading]
      exact pow_le_pow_left' (candidateTrial_none_le_half leading) trials)
  norm_num at h
  apply h.trans
  have hPrep : preparationSteps bits ≤ 4 * bits.length + 10 := by
    unfold preparationSteps
    split_ifs <;> omega
  calc
    _ ≤ ((4 * bits.length + 10 + 2 * block : Nat) : ℝ≥0∞) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      exact add_le_add (by exact_mod_cast hPrep) (by rw [mul_comm])
    _ ≤ ((24 * (bits.length + 1) : Nat) : ℝ≥0∞) := by
      exact_mod_cast (by dsimp [block]; omega : 4 * bits.length + 10 + 2 * block ≤ 24 * (bits.length + 1))

/-- The fixed program has linear expected transition count on every raw
bitstring, including empty and malformed inputs. Unbounded rejection paths
are retained rather than claimed to have a finite worst-case budget. -/
theorem expectedSteps_le (input : List Bool) :
    expectedSteps program input ≤ (24 * (input.length + 1) : Nat) := by
  cases hReverse : input.reverse with
  | nil =>
      have hInput : input = [] := List.reverse_eq_nil_iff.mp hReverse
      subst input
      exact (expectedSteps_le_of_haltsWithin empty_haltsWithin).trans (by norm_num)
  | cons last rest =>
      have hInput : input = rest.reverse ++ [last] := by
        simpa using congrArg List.reverse hReverse
      subst input
      cases last with
      | false =>
          exact (expectedSteps_le_of_haltsWithin (malformed_haltsWithin rest.reverse)).trans (by
            exact_mod_cast (by simp; omega : 2 * (rest.reverse ++ [false]).length + 8 ≤
              24 * ((rest.reverse ++ [false]).length + 1)))
      | true =>
          by_cases hRest : rest.reverse = []
          · simp only [hRest, List.nil_append]
            exact (expectedSteps_le_of_haltsWithin one_haltsWithin).trans (by norm_num)
          · exact expectedSteps_canonical rest.reverse hRest

theorem expectedPolynomialTime : ExpectedPolynomialTime program := by
  refine ⟨fun n => 24 * (n + 1), ?_, expectedSteps_le⟩
  exact (PolynomiallyBounded.const 24).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

/-- Cofinal complete-trial inspections give the exact limiting mass of each
accepted bitstring. No normalization is performed on finite-budget laws. -/
theorem outputMass_geometric (leading : List Bool) (hLeading : leading ≠ [])
    (output : List Bool) :
    let bits := leading ++ [true]
    outputMass program bits output = candidateTrial bits (some output) *
      (1 - candidateTrial bits none)⁻¹ := by
  dsimp only
  let bits := leading ++ [true]
  let block := 10 * bits.length + 7
  have hSup : outputMass program bits output =
      ⨆ trials : Nat, evalWithin program bits
        (preparationSteps bits + trials * block) (some output) := by
    apply le_antisymm
    · apply iSup_le
      intro steps
      have hBound : steps ≤ preparationSteps bits + steps * block := by
        have h := Nat.le_mul_of_pos_right steps (by dsimp [block]; omega : 0 < block)
        omega
      exact (evalWithin_some_monotone program bits output hBound).trans
        (le_iSup (fun trials => evalWithin program bits
          (preparationSteps bits + trials * block) (some output)) steps)
    · unfold outputMass
      exact iSup_le fun trials => le_iSup
        (fun steps => evalWithin program bits steps (some output))
        (preparationSteps bits + trials * block)
  rw [hSup]
  dsimp only [bits, block]
  simp_rw [eval_prepared_trials leading hLeading, trialWeights_some]
  rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]

private theorem retry_factor (modulus : List Bool) :
    (1 - candidateTrial modulus none)⁻¹ =
      ((2 ^ modulus.length : Nat) : ℝ≥0∞) / (Binary.value modulus : ℝ≥0∞) := by
  let N : ℝ≥0∞ := (2 ^ modulus.length : Nat)
  let q : ℝ≥0∞ := Binary.value modulus
  have hN0 : N ≠ 0 := by simp [N]
  have hNtop : N ≠ ⊤ := by simp [N]
  have hqN : q ≤ N := by
    dsimp [q, N]
    exact_mod_cast (Binary.value_lt modulus).le
  have hqDiv : q / N ≤ 1 := (ENNReal.div_le_iff hN0 hNtop).mpr (by simpa using hqN)
  rw [candidateTrial_none, ENNReal.natCast_sub]
  change (1 - (N - q) / N)⁻¹ = N / q
  rw [ENNReal.sub_div (by intro _ _; exact hN0), ENNReal.div_self hN0 hNtop,
    ENNReal.sub_sub_cancel (by simp) hqDiv]
  exact ENNReal.inv_div (Or.inl hNtop) (Or.inl hN0)

private theorem candidateTrial_other (modulus output : List Bool)
    (hOutput : ∀ a : Fin (Binary.value modulus), Binary.encode modulus.length a.val ≠ output) :
    candidateTrial modulus (some output) = 0 := by
  rw [candidateTrial_number, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  by_cases ha : a.val < Binary.value modulus
  · have hCode := hOutput ⟨a.val, ha⟩
    simp [ha, Ne.symm hCode]
  · simp [ha]

/-- For a nonunit canonical positive modulus the output limit is exactly
uniform on the residues below it. This is equality of PMFs, not a statistical
approximation and not a conditional finite-budget distribution. -/
theorem evalLimit_canonical (leading : List Bool) (hLeading : leading ≠ [])
    [Nonempty (Fin (Binary.value (leading ++ [true])))] :
    let bits := leading ++ [true]
    evalLimit program bits (expectedPolynomialTime.almostSureHalts bits) =
      (uniform (Fin (Binary.value bits))).map (fun a => Binary.encode bits.length a.val) := by
  classical
  dsimp only
  let bits := leading ++ [true]
  ext output
  change outputMass program bits output =
    ((uniform (Fin (Binary.value bits))).map (fun a => Binary.encode bits.length a.val)) output
  rw [outputMass_geometric leading hLeading, retry_factor bits]
  by_cases hCode : ∃ a : Fin (Binary.value bits), Binary.encode bits.length a.val = output
  · obtain ⟨a, rfl⟩ := hCode
    rw [candidateTrial_encoded bits ⟨a.val, a.isLt.trans (Binary.value_lt bits)⟩ a.isLt]
    rw [PMF.map_apply, tsum_eq_single a]
    · simp only [uniform, PMF.uniformOfFintype_apply,
        Fintype.card_fin, div_eq_mul_inv]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (a := ((2 ^ bits.length : Nat) : ℝ≥0∞))
        (by simp) (by simp), one_mul]
      simp
    · intro other hOther
      have hDifferent : Binary.encode bits.length a.val ≠ Binary.encode bits.length other.val := by
        intro h
        have hv := congrArg Binary.value h
        rw [Binary.value_encode (a.isLt.trans (Binary.value_lt bits)),
          Binary.value_encode (other.isLt.trans (Binary.value_lt bits))] at hv
        exact hOther (Fin.ext hv.symm)
      simp [hDifferent]
  · have hOther : ∀ a : Fin (Binary.value bits), Binary.encode bits.length a.val ≠ output := by
      simpa only [not_exists] using hCode
    rw [candidateTrial_other bits output hOther, zero_mul, PMF.map_apply]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    simp [Ne.symm (hOther a)]

/-- The special unit-modulus path realizes its sole possible output exactly. -/
theorem evalLimit_one :
    evalLimit program [true] (expectedPolynomialTime.almostSureHalts [true]) =
      PMF.pure [false] := by
  ext output
  change outputMass program [true] output = _
  rw [outputMass_eq_of_haltsWithin one_haltsWithin, one_eval]
  simp [PMF.pure_apply]

/-- Exact uniform residues for every canonical positive modulus, including
one. The family of output codes is fixed-width little endian. -/
theorem evalLimit_uniform (leading : List Bool)
    [Nonempty (Fin (Binary.value (leading ++ [true])))] :
    let bits := leading ++ [true]
    evalLimit program bits (expectedPolynomialTime.almostSureHalts bits) =
      (uniform (Fin (Binary.value bits))).map (fun a => Binary.encode bits.length a.val) := by
  by_cases hLeading : leading = []
  · subst leading
    simp only [List.nil_append]
    rw [evalLimit_one]
    ext output
    simp only [uniform, PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp [tsum_fintype, Binary.value, Binary.encode, PMF.pure_apply]
  · exact evalLimit_canonical leading hLeading

/-- One fixed finite program, with its all-input expected-time certificate,
implements the ideal uniform distribution for every positive binary modulus. -/
theorem evalLimit_nat (q : Nat) [NeZero q] :
    evalLimit program q.bits (expectedPolynomialTime.almostSureHalts q.bits) =
      (uniform (Fin q)).map (fun a => Binary.encode q.bits.length a.val) := by
  obtain ⟨leading, hLeading⟩ := Binary.nat_bits_canonical q (NeZero.ne q)
  have hValue : Binary.value (leading ++ [true]) = q := by
    rw [← hLeading, Binary.value_nat_bits]
  have : Nonempty (Fin (Binary.value (leading ++ [true]))) := by
    rw [hValue]
    infer_instance
  subst q
  simpa only [hLeading] using evalLimit_uniform leading

/-- Decoding uses the same finite-width codec as the mathematical scalar
representation. No decoder is installed as a machine instruction. -/
theorem evalLimit_nat_decoded (q : Nat) [NeZero q] :
    let code := Binary.fin q q.bits.length (by simpa using (Binary.value_lt q.bits).le)
    (evalLimit program q.bits (expectedPolynomialTime.almostSureHalts q.bits)).map code.decode =
      (uniform (Fin q)).map some := by
  dsimp only
  rw [evalLimit_nat, PMF.map_comp]
  congr 1
  funext a
  exact (Binary.fin q q.bits.length (by simpa using (Binary.value_lt q.bits).le)).decode_encode a

/-- The actual general sampler has no finite every-branch budget already at
modulus three. Almost-sure expected stopping is not worst-case stopping. -/
theorem not_haltsWithin_three (bound : Nat) :
    ¬ HaltsWithin program [true, true] bound := by
  intro h
  let block := 10 * ([true, true] : List Bool).length + 7
  have hBudget : bound ≤ preparationSteps [true, true] + (bound + 1) * block := by
    have hMul := Nat.le_mul_of_pos_right (bound + 1) (by decide : 0 < block)
    omega
  have hz : timeoutProbability program [true, true]
      (preparationSteps [true, true] + (bound + 1) * block) = 0 :=
    evalWithin_no_timeout program [true, true] _ (h.mono hBudget)
  have hGeometric := timeout_prepared_trials [true] (by decide) (bound + 1)
  have hzPower : (candidateTrial [true, true] none) ^ (bound + 1) = 0 :=
    hGeometric.symm.trans hz
  have hRatio : candidateTrial [true, true] none ≠ 0 := by
    rw [candidateTrial_none]
    norm_num [Binary.value]
  exact pow_ne_zero _ hRatio hzPower

theorem not_polynomialTime : ¬ PolynomialTime program := by
  rintro ⟨budget, _, hHalt⟩
  exact not_haltsWithin_three (budget 2) (hHalt [true, true])

end Machine.RejectionSampling
