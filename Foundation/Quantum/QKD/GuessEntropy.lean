import Foundation.Quantum.QKD.GuessAdditionalLeak
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Operational guessing entropy and finite-public-message chain rules.
This is defined from the optimal measurement success probability. Equality
with the order-optimization definition of conditional min-entropy, and
smoothing, are separate unproved obligations, not definitional assertions. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X L C : Type} [Fintype X] [Fintype L] [Fintype C] {e : Space}

theorem card_mul_guessing_ge_one (ρ : CQ X e) : 1 ≤ Fintype.card X * guessingProbability ρ := by
  classical
  calc
    (1 : ℝ) = ∑ x, (ρ.block x).trace.re := by
      rw [← Complex.re_sum, ρ.normalized]
      rfl
    _ ≤ ∑ _ : X, guessingProbability ρ := Finset.sum_le_sum (fun x _ => by
      rw [← score_constantMeasurement]
      exact score_le_guessingProbability _ _)
    _ = _ := by simp

theorem guessingProbability_pos (ρ : CQ X e) : 0 < guessingProbability ρ := by
  have h := card_mul_guessing_ge_one ρ
  have hn : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  by_contra hp
  have : Fintype.card X * guessingProbability ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn (le_of_not_gt hp)
  linarith

/-- Entropy measured in bits, defined operationally through optimal guessing. -/
def guessingEntropy (ρ : CQ X e) : ℝ := -Real.logb 2 (guessingProbability ρ)

theorem guessingEntropy_nonneg (ρ : CQ X e) : 0 ≤ guessingEntropy ρ := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (guessingProbability_pos ρ)
    (guessingProbability_le_one ρ)
  simp only [Real.logb_one] at h
  exact neg_nonneg.mpr h

/-- Old public information is part of the retained side system. -/
def publicGuessingEntropy (ρ : CQ (X × L) e) : ℝ := guessingEntropy (withPublic ρ)

/-- A newly disclosed finite message costs at most log₂ |C| operational bits.
No independent prior public transcript or classical Eve is assumed. -/
theorem additional_entropy (ρ : CQ ((X × C) × L) e) :
    publicGuessingEntropy (forgetMessage ρ) - Real.logb 2 (Fintype.card C) ≤
      publicGuessingEntropy (withPublic ρ) := by
  have h := additional_leakage ρ
  rw [← withPublic_optimal, ← withPublic_optimal] at h
  have hp := guessingProbability_pos (withPublic (withPublic ρ))
  have hq := guessingProbability_pos (withPublic (forgetMessage ρ))
  have hc : (0 : ℝ) < Fintype.card C := by
    have : Nonempty C := Nonempty.map (fun p : (X × C) × L => p.1.2) ρ.nonempty
    exact_mod_cast Fintype.card_pos
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) hp h
  rw [Real.logb_mul (ne_of_gt hc) (ne_of_gt hq)] at hl
  unfold publicGuessingEntropy guessingEntropy
  linarith

theorem disclosure_entropy [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : CQ (X × L) e) (message : X → L → C) :
    publicGuessingEntropy ρ - Real.logb 2 (Fintype.card C) ≤
      publicGuessingEntropy (withPublic (disclose ρ message)) := by
  simpa only [forget_disclose] using additional_entropy (disclose ρ message)

/-- A message containing r bits loses at most r operational entropy bits. -/
theorem bit_disclosure_entropy [DecidableEq X] [DecidableEq L]
    (ρ : CQ (X × L) e) (r : Nat) (message : X → L → (Fin r → Fin 2)) :
    publicGuessingEntropy ρ - r ≤
      publicGuessingEntropy (withPublic (disclose ρ message)) := by
  have h := disclosure_entropy ρ message
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] using h

end
end Foundation.Quantum.QKD.Guessing
