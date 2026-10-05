import Foundation.Crypto.Semantics.Machine.RetryExpectation

namespace Machine

open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

/-- Timeout probability from retained physical tapes, rather than a fresh
input load. The evaluator and its charged transitions are unchanged. -/
noncomputable def timeoutProbabilityFrom (p : Program) (start : Configuration)
    (steps : Nat) : ℝ≥0∞ := ((evalConfigWithin p start steps).map report) none

/-- The usual halting-time tail sum from an arbitrary retained configuration.
This permits caller data and head positions to remain on the tapes. -/
noncomputable def expectedStepsFrom (p : Program) (start : Configuration) : ℝ≥0∞ :=
  ∑' steps : Nat, timeoutProbabilityFrom p start steps

theorem timeoutProbabilityFrom_initial (p : Program) (input : List Bool) (steps : Nat) :
    timeoutProbabilityFrom p (Configuration.initial input) steps = timeoutProbability p input steps := by
  simp [timeoutProbabilityFrom, timeoutProbability, evalWithin, report,
    Foundation.Probability.eventProb, PMF.toOuterMeasure_apply_singleton]

theorem expectedStepsFrom_initial (p : Program) (input : List Bool) :
    expectedStepsFrom p (Configuration.initial input) = expectedSteps p input := by
  simp only [expectedStepsFrom, expectedSteps, timeoutProbabilityFrom_initial]

private theorem reported_some_monotone (p : Program) (start : Configuration) (bits : List Bool) :
    Monotone (fun steps => ((evalConfigWithin p start steps).map report) (some bits)) := by
  classical
  apply monotone_nat_of_le_succ
  intro steps
  rw [evalConfigWithin, PMF.map_apply, PMF.map_bind, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  by_cases h : some bits = report c
  · have hc : c.halted = true := by cases hh : c.halted <;> simp_all [report]
    have hs : stepPMF p c = PMF.pure c := by simp [stepPMF, next, hc]
    rw [hs, PMF.pure_map]
    simp [h]
  · simp [h]

private theorem reported_mass (p : Program) (start : Configuration) (steps : Nat) :
    (∑' bits, ((evalConfigWithin p start steps).map report) (some bits)) +
      timeoutProbabilityFrom p start steps = 1 := by
  have h := (Equiv.optionEquivSumPUnit.{0, 0} (List Bool)).symm.tsum_eq
    (fun value => ((evalConfigWithin p start steps).map report) value)
  have h' := h.trans (PMF.tsum_coe _)
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at h'
  simpa [timeoutProbabilityFrom] using h'

theorem timeoutProbabilityFrom_antitone (p : Program) (start : Configuration) :
    Antitone (timeoutProbabilityFrom p start) := by
  have hMass (steps : Nat) : timeoutProbabilityFrom p start steps =
      1 - ∑' bits, ((evalConfigWithin p start steps).map report) (some bits) := by
    apply ENNReal.eq_sub_of_add_eq
    · exact ne_of_lt ((le_add_right le_rfl).trans_lt (by rw [reported_mass]; simp))
    · simpa [add_comm] using reported_mass p start steps
  intro i j hij
  rw [hMass i, hMass j]
  exact tsub_le_tsub_left
    (ENNReal.tsum_le_tsum (fun bits => reported_some_monotone p start bits hij)) 1

/-- Geometric retry bounds charge preparation and continuation work from
retained configurations exactly as for the original fresh-input evaluator. -/
theorem expectedStepsFrom_le_of_timeout_blocks_after {p : Program} {start : Configuration}
    (preparation block : Nat) [NeZero block] (ratio : ℝ≥0∞)
    (h : ∀ trials : Nat,
      timeoutProbabilityFrom p start (preparation + trials * block) ≤ ratio ^ trials) :
    expectedStepsFrom p start ≤ (preparation : ℝ≥0∞) + (block : ℝ≥0∞) * (1-ratio)⁻¹ := by
  have hEach (steps : Nat) : timeoutProbabilityFrom p start (steps+preparation) ≤
      ratio ^ (steps/block) := by
    exact (timeoutProbabilityFrom_antitone p start (by
      have := Nat.div_mul_le_self steps block
      omega : preparation+(steps/block)*block ≤ steps+preparation)).trans (h (steps/block))
  have hTail : (∑' steps : Nat, timeoutProbabilityFrom p start (steps+preparation)) ≤
      (block : ℝ≥0∞) * (1-ratio)⁻¹ := by
    calc
      _ ≤ ∑' steps : Nat, ratio ^ (steps/block) := ENNReal.tsum_le_tsum hEach
      _ = ∑' pair : Nat × Fin block, ratio ^ pair.1 := by
        simpa using (Nat.divModEquiv block).tsum_eq (fun pair : Nat × Fin block => ratio ^ pair.1)
      _ = _ := by
        rw [ENNReal.tsum_prod']
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  unfold expectedStepsFrom
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := preparation)]
  apply add_le_add _ hTail
  calc
    _ ≤ ∑ _steps ∈ Finset.range preparation, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun steps _ => PMF.coe_le_one _ _)
    _ = _ := by simp

/-- Unrenormalized eventual output probability from retained physical tapes. -/
noncomputable def outputMassFrom (p : Program) (start : Configuration) (bits : List Bool) : ℝ≥0∞ :=
  ⨆ steps : Nat, ((evalConfigWithin p start steps).map report) (some bits)

private theorem tsum_iSup_of_monotone {α : Type*} (f : Nat → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

theorem outputMassFrom_tsum_le_one (p : Program) (start : Configuration) :
    (∑' bits, outputMassFrom p start bits) ≤ 1 := by
  unfold outputMassFrom
  rw [tsum_iSup_of_monotone _ (fun bits => reported_some_monotone p start bits)]
  apply iSup_le
  intro steps
  exact (le_add_right le_rfl).trans (le_of_eq (reported_mass p start steps))

/-- A normalized proposed law whose every output probability is present in
native execution already identifies that execution exactly. This uses the
operational mass bound, not conditional renormalization of timeouts. -/
theorem outputMassFrom_eq_of_dominates (p : Program) (start : Configuration)
    (law : PMF (List Bool)) (h : ∀ bits, law bits ≤ outputMassFrom p start bits) :
    ∀ bits, outputMassFrom p start bits = law bits := by
  classical
  intro bits
  have splitMass (f : List Bool → ℝ≥0∞) :
      (∑' other, f other) = f bits + ∑' other, if other = bits then 0 else f other := by
    apply (ENNReal.tsum_eq_add_tsum_ite (f := f) bits).trans
    congr 1
    apply tsum_congr
    intro other
    by_cases hSame : other = bits <;> simp [hSame]
  apply le_antisymm _ (h bits)
  let remainder := ∑' other, if other = bits then (0 : ℝ≥0∞) else law other
  have hRemainder : remainder ≠ ∞ := by
    apply ne_of_lt
    calc
      remainder ≤ ∑' other, law other := ENNReal.tsum_le_tsum (fun other => by split_ifs <;> simp)
      _ = 1 := PMF.tsum_coe law
      _ < ∞ := by simp
  apply ENNReal.le_of_add_le_add_right hRemainder
  calc
    outputMassFrom p start bits + remainder ≤ outputMassFrom p start bits +
        ∑' other, if other = bits then 0 else outputMassFrom p start other := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro other
      split_ifs <;> simp [h other]
    _ = ∑' other, outputMassFrom p start other := by
      exact (splitMass (outputMassFrom p start)).symm
    _ ≤ 1 := outputMassFrom_tsum_le_one p start
    _ = law bits + remainder := by
      exact (PMF.tsum_coe law).symm.trans (splitMass (fun other => law other))

end Machine
