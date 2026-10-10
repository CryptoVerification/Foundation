import Foundation.Quantum.QKD.Sampling
import Foundation.Crypto.Semantics.Probability.Facts

/-! A finite-population detection bound after an arbitrary distribution of
error patterns, with fresh uniform sampling independent of that pattern.
Correlations among errors are allowed. No quantum phase-error claim is made. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
open Foundation.Probability
open scoped ENNReal
variable {α : Type*} [DecidableEq α]

def missedErrorBound (U : Finset α) (k bad : Nat) : ℝ≥0∞ :=
  (Nat.choose (U.card - bad) k : ℝ≥0∞) / (Nat.choose U.card k : ℝ≥0∞)

/-- At least `bad` erroneous positions in the population imply this sampling bound. -/
theorem undetected_le (U E : Finset α) (k bad : Nat) (hk : k ≤ U.card)
    (hbad : bad ≤ (E ∩ U).card) :
    eventProb (sample U k hk) (undetected E) ≤ missedErrorBound U k bad := by
  rw [undetected_probability]
  apply ENNReal.div_le_div_right
  have hc : (U \ E).card ≤ U.card - bad := by
    rw [Finset.card_sdiff]
    omega
  exact_mod_cast Nat.choose_le_choose k hc

/-- First generate any possibly correlated error pattern, then independently choose the test sample. -/
def experiment (p : ProbComp (Finset α)) (U : Finset α) (k : Nat) (hk : k ≤ U.card) :
    ProbComp (Finset α × Finset α) :=
  p.bind (fun E => (sample U k hk).map (fun T => (E,T)))

def badUndetected (U : Finset α) (bad : Nat) (r : Finset α × Finset α) : Prop :=
  bad ≤ (r.1 ∩ U).card ∧ undetected r.1 r.2

/-- The test failure bound holds without an independent-bit or product-distribution premise. -/
theorem experiment_bound (p : ProbComp (Finset α)) (U : Finset α) (k bad : Nat) (hk : k ≤ U.card) :
    eventProb (experiment p U k hk) (badUndetected U bad) ≤ missedErrorBound U k bad := by
  apply eventProb_bind_le
  intro E
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hbad : bad ≤ (E ∩ U).card
  · have hs : (fun T => (E,T)) ⁻¹' {r | badUndetected U bad r} = {T | undetected E T} := by
      ext T
      simp [badUndetected, hbad]
    rw [hs]
    exact undetected_le U E k bad hk hbad
  · have hs : (fun T => (E,T)) ⁻¹' {r | badUndetected U bad r} = ∅ := by
      ext T
      simp [badUndetected, hbad]
    rw [hs]
    simp

end
end Foundation.Quantum.QKD.Sampling
