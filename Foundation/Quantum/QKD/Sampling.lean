import Foundation.Crypto.Semantics.Probability.Comp
import Mathlib.Data.Finset.Powerset

/-! Exact sampling without replacement for an arbitrary fixed error pattern.
No independence between the individual errors is assumed. This is a classical
sampling lemma, not a quantum phase-error estimation theorem. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
open Foundation.Probability
open scoped ENNReal
variable {α : Type*} [DecidableEq α]

/-- The draw is uniform over all subsets with exactly k tested positions. -/
def sample (U : Finset α) (k : Nat) (hk : k ≤ U.card) : ProbComp (Finset α) :=
  PMF.uniformOfFinset (U.powersetCard k) (Finset.powersetCard_nonempty.mpr hk)

/-- Accepted here means that the selected sample contains no error. -/
abbrev undetected (E T : Finset α) : Prop := Disjoint T E

theorem successful_samples (U E : Finset α) (k : Nat) :
    (U.powersetCard k).filter (fun T => undetected E T) = (U \ E).powersetCard k := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard, undetected]
  constructor
  · rintro ⟨⟨hTU,hcard⟩,hTE⟩
    exact ⟨Finset.subset_sdiff.mpr ⟨hTU,hTE⟩, hcard⟩
  · rintro ⟨hT,hcard⟩
    obtain ⟨hTU,hTE⟩ := Finset.subset_sdiff.mp hT
    exact ⟨⟨hTU,hcard⟩,hTE⟩

/-- An exact finite-population probability, including correlated or adversarial error patterns. -/
theorem undetected_probability (U E : Finset α) (k : Nat) (hk : k ≤ U.card) :
    eventProb (sample U k hk) (undetected E) =
      (Nat.choose (U \ E).card k : ℝ≥0∞) / (Nat.choose U.card k : ℝ≥0∞) := by
  unfold eventProb sample
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  rw [successful_samples, Finset.card_powersetCard, Finset.card_powersetCard]

/-- Testing more positions than the number of error-free positions cannot miss all errors. -/
theorem undetected_zero (U E : Finset α) (k : Nat) (hk : k ≤ U.card)
    (hbad : (U \ E).card < k) : eventProb (sample U k hk) (undetected E) = 0 := by
  rw [undetected_probability, Nat.choose_eq_zero_of_lt hbad]
  simp

end
end Foundation.Quantum.QKD.Sampling
