import Foundation.Quantum.QKD.Sampling
import Foundation.Quantum.RecordObservation
import Mathlib.Data.Nat.Choose.Cast

/-! Actual inclusion probabilities in uniform fixed-size sampling without
replacement. Their counting proof imposes no distribution on the population. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [DecidableEq α]

theorem subset_probability (U E : Finset α) (k : Nat) (hk : k ≤ U.card)
    (hEU : E ⊆ U) (hEk : E.card ≤ k) :
    eventProb (sample U k hk) (fun T => E ⊆ T) =
      (Nat.choose (U.card-E.card) (k-E.card) : ℝ≥0∞) / (Nat.choose U.card k : ℝ≥0∞) := by
  unfold eventProb sample
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  rw [Finset.card_filter_powersetCard_subset E U k hEU hEk, Finset.card_powersetCard]

theorem subset_too_large (U E : Finset α) (k : Nat) (hk : k ≤ U.card)
    (hEk : k < E.card) : eventProb (sample U k hk) (fun T => E ⊆ T) = 0 := by
  unfold eventProb sample
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  have he : (U.powersetCard k).filter (fun T => E ⊆ T) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro T hT hET
    have hc := Finset.card_le_card hET
    have hcard := (Finset.mem_powersetCard.mp hT).2
    omega
  simp only [Set.mem_ofPred_eq, he, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]

theorem singleton_probability_real (U : Finset α) (k : Nat) (hk : k ≤ U.card)
    (i : α) (hi : i ∈ U) :
    (eventProb (sample U k hk) (fun T => i ∈ T)).toReal = (k : ℝ)/U.card := by
  have hn : 0 < U.card := Finset.card_pos.mpr ⟨i,hi⟩
  have hn' : (U.card : ℝ) ≠ 0 := by positivity
  have hc : (Nat.choose U.card k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have he : (fun T : Finset α => i ∈ T) = (fun T => ({i} : Finset α) ⊆ T) := by
    funext T
    simp
  rw [he]
  by_cases h1 : 1 ≤ k
  · rw [subset_probability U {i} k hk (by simpa using hi) (by simpa using h1)]
    simp only [Finset.card_singleton, ENNReal.toReal_div, ENNReal.toReal_natCast]
    have hid := Nat.choose_mul (n := U.card) (k := k) (s := 1) h1
    simp only [Nat.choose_one_right] at hid
    have hid' : (Nat.choose U.card k : ℝ) * k = U.card * (Nat.choose (U.card-1) (k-1) : ℝ) := by
      exact_mod_cast hid
    field_simp
    nlinarith [hid']
  · have hk0 : k = 0 := by omega
    subst k
    rw [subset_too_large U {i} 0 hk (by simp)]
    simp

theorem pair_probability_real (U : Finset α) (k : Nat) (hk : k ≤ U.card)
    (i j : α) (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) :
    (eventProb (sample U k hk) (fun T => i ∈ T ∧ j ∈ T)).toReal =
      (k : ℝ)*(k-1) / ((U.card : ℝ)*(U.card-1)) := by
  have hcard : ({i,j} : Finset α).card = 2 := by simp [hij]
  have hn : 2 ≤ U.card := by
    have h := Finset.card_le_card (show ({i,j} : Finset α) ⊆ U by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj)
    omega
  have hn' : (U.card : ℝ) ≠ 0 := by positivity
  have hn1 : (U.card : ℝ)-1 ≠ 0 := by
    have h : (2 : ℝ) ≤ U.card := by exact_mod_cast hn
    linarith
  have hc : (Nat.choose U.card k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have he : (fun T : Finset α => i ∈ T ∧ j ∈ T) = (fun T => ({i,j} : Finset α) ⊆ T) := by
    funext T
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [he]
  by_cases h2 : 2 ≤ k
  · rw [subset_probability U {i,j} k hk (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj) (by simpa [hcard] using h2)]
    simp only [hcard, ENNReal.toReal_div, ENNReal.toReal_natCast]
    have hid := Nat.choose_mul (n := U.card) (k := k) (s := 2) h2
    have hid' : (Nat.choose U.card k : ℝ) * (Nat.choose k 2 : ℝ) =
        (Nat.choose U.card 2 : ℝ) * (Nat.choose (U.card-2) (k-2) : ℝ) := by exact_mod_cast hid
    rw [Nat.cast_choose_two, Nat.cast_choose_two] at hid'
    field_simp
    nlinarith [hid']
  · rw [subset_too_large U {i,j} k hk (by omega)]
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> simp

end
end Foundation.Quantum.QKD.Sampling
