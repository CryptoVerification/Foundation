import Foundation.Crypto.Semantics.Machine.ExpectedExecution
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Equiv.Option

namespace Machine

open scoped ENNReal Topology

/-- A branch that has already halted retains its output probability when
one more round is inspected. New halting branches may add probability. -/
theorem evalWithin_some_monotone (p : Program) (input bits : List Bool) :
    Monotone (fun steps => evalWithin p input steps (some bits)) := by
  classical
  apply monotone_nat_of_le_succ
  intro steps
  unfold evalWithin
  rw [evalConfigWithin, PMF.map_apply, PMF.map_bind, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  by_cases h : some bits = (if c.halted then some c.outputBits else none)
  · have hc : c.halted = true := by
      cases hh : c.halted <;> simp_all
    have hs : stepPMF p c = PMF.pure c := by simp [stepPMF, next, hc]
    rw [hs, PMF.pure_map]
    simp [h]
  · simp [h]

/-- Probability of eventually returning exactly `bits`, defined directly
from the existing finite operational evaluator. No timeout mass is
renormalized, and no stopping-bound witness enters this definition. -/
noncomputable def outputMass (p : Program) (input bits : List Bool) : ℝ≥0∞ :=
  ⨆ steps : Nat, evalWithin p input steps (some bits)

private theorem tsum_iSup_of_monotone {α : Type*} (f : Nat → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

private theorem evalWithin_mass (p : Program) (input : List Bool) (steps : Nat) :
    (∑' bits, evalWithin p input steps (some bits)) + timeoutProbability p input steps = 1 := by
  have h := (Equiv.optionEquivSumPUnit.{0, 0} (List Bool)).symm.tsum_eq
    (fun value => evalWithin p input steps value)
  have h' := h.trans (PMF.tsum_coe _)
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at h'
  simpa [timeoutProbability, Foundation.Probability.eventProb,
    PMF.toOuterMeasure_apply_singleton] using h'

/-- Inspecting more rounds cannot increase the probability of still running. -/
theorem timeoutProbability_antitone (p : Program) (input : List Bool) :
    Antitone (timeoutProbability p input) := by
  have hMass (steps : Nat) : timeoutProbability p input steps =
      1 - ∑' bits, evalWithin p input steps (some bits) := by
    apply ENNReal.eq_sub_of_add_eq
    · exact ne_of_lt ((le_add_right le_rfl).trans_lt
        (by rw [evalWithin_mass]; simp))
    · simpa [add_comm] using evalWithin_mass p input steps
  intro i j hij
  rw [hMass i, hMass j]
  exact tsub_le_tsub_left
    (ENNReal.tsum_le_tsum (fun bits => evalWithin_some_monotone p input bits hij)) 1

/-- Eventual output mass is at most one, including for programs that do
not halt with probability one. -/
theorem outputMass_tsum_le_one (p : Program) (input : List Bool) :
    (∑' bits, outputMass p input bits) ≤ 1 := by
  unfold outputMass
  rw [tsum_iSup_of_monotone _ (fun bits => evalWithin_some_monotone p input bits)]
  apply iSup_le
  intro steps
  exact (le_add_right le_rfl).trans (le_of_eq (evalWithin_mass p input steps))

/-- Vanishing timeout probability gives full output mass. This proves
normalization before constructing a probability mass function. -/
theorem outputMass_tsum_eq_one {p : Program} {input : List Bool}
    (h : AlmostSureHalts p input) : (∑' bits, outputMass p input bits) = 1 := by
  have hMass (steps : Nat) :
      (∑' bits, evalWithin p input steps (some bits)) =
        1 - timeoutProbability p input steps := by
    exact ENNReal.eq_sub_of_add_eq
      (ne_of_lt ((timeoutProbability_le_one p input steps).trans_lt (by simp)))
      (evalWithin_mass p input steps)
  have hLimit : Filter.Tendsto
      (fun steps => ∑' bits, evalWithin p input steps (some bits))
      Filter.atTop (𝓝 1) := by
    simp_rw [hMass]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl (by simp))
  unfold outputMass
  rw [tsum_iSup_of_monotone _ (fun bits => evalWithin_some_monotone p input bits)]
  apply iSup_eq_of_tendsto
  · intro i j hij
    exact ENNReal.tsum_le_tsum (fun bits => evalWithin_some_monotone p input bits hij)
  · exact hLimit

/-- Unbounded operational output for a program whose timeout probability
vanishes. Its probabilities are the unmodified eventual output masses. -/
noncomputable def evalLimit (p : Program) (input : List Bool)
    (h : AlmostSureHalts p input) : PMF (List Bool) :=
  ⟨outputMass p input, ENNReal.summable.hasSum_iff.mpr (outputMass_tsum_eq_one h)⟩

@[simp] theorem evalLimit_apply (p : Program) (input : List Bool)
    (h : AlmostSureHalts p input) (bits : List Bool) :
    evalLimit p input h bits = outputMass p input bits := rfl

/-- With an all-branch stopping budget, the eventual probability is already
attained at that finite budget. -/
theorem outputMass_eq_of_haltsWithin {p : Program} {input : List Bool}
    {bound : Nat} (h : HaltsWithin p input bound) (bits : List Bool) :
    outputMass p input bits = evalWithin p input bound (some bits) := by
  apply le_antisymm
  · apply iSup_le
    intro steps
    rcases le_total steps bound with hLe | hLe
    · exact evalWithin_some_monotone p input bits hLe
    · rw [evalWithin_eq_of_haltsWithin p input steps bound (h.mono hLe) h]
  · exact le_iSup (fun steps => evalWithin p input steps (some bits)) bound

/-- The unbounded distribution agrees exactly with the existing bounded
evaluator whenever a universal stopping bound is available. -/
theorem evalLimit_map_some_of_haltsWithin {p : Program} {input : List Bool}
    {bound : Nat} (h : HaltsWithin p input bound) (hAS : AlmostSureHalts p input) :
    (evalLimit p input hAS).map some = evalWithin p input bound := by
  ext value
  cases value with
  | none =>
      have hNone : evalWithin p input bound none = 0 := by
        have hz := evalWithin_no_timeout p input bound h
        change (evalWithin p input bound).toOuterMeasure {none} = 0 at hz
        rwa [PMF.toOuterMeasure_apply_singleton] at hz
      simp [PMF.map_apply, hNone]
  | some bits =>
      simp [PMF.map_apply, evalLimit_apply, outputMass_eq_of_haltsWithin h]

end Machine
