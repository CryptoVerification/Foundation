import Foundation.Quantum.QKD.BB84PairwiseSelection
import Foundation.Quantum.QKD.Sampling
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Dist

/-! Exact finite pairwise one-out-of-two sampling with an independent
fixed-size test set (Bouman--Fehr Example 5). The worst-case error is computed
from finite event counts; no unproved concentration bound is assumed. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Pattern (n : Nat) := Fin n × Fin 2 → Fin 2
abbrev Configuration (n : Nat) := (Fin n → Fin 2) × Finset (Fin n)

def configurations (n k : Nat) : Finset (Configuration n) :=
  Finset.univ.product (Finset.univ.powersetCard k)

theorem configurations_card (n k : Nat) : (configurations n k).card = 2^n * Nat.choose n k := by
  simp [configurations]

theorem configurations_nonempty (n k : Nat) (hk : k ≤ n) : (configurations n k).Nonempty := by
  apply Finset.nonempty_product.mpr
  exact ⟨Finset.univ_nonempty, Finset.powersetCard_nonempty.mpr (by simpa using hk)⟩

def distribution (n k : Nat) (hk : k ≤ n) : PMF (Configuration n) :=
  PMF.uniformOfFinset (configurations n k) (configurations_nonempty n k hk)

def flip (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

def tested {n : Nat} (q : Pattern n) (c : Configuration n) : Nat :=
  (c.2.filter (fun i => q (i,c.1 i) = 1)).card

def remaining {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) : Nat :=
  (Finset.univ.filter (fun i => q (i,flip (s i)) = 1)).card

/-- Integer-scaled deviation: for positive n,k this bounds the deviation of
relative weights by gap/(n*k), with no floating-point or rounding assumption. -/
def bad {n : Nat} (k gap : Nat) (q : Pattern n) (c : Configuration n) : Prop :=
  gap < Nat.dist (n * tested q c) (k * remaining q c.1)

instance {n : Nat} (k gap : Nat) (q : Pattern n) : DecidablePred (bad k gap q) :=
  fun _ => inferInstanceAs (Decidable (_ < _))

def badCount (n k gap : Nat) (q : Pattern n) : Nat :=
  ((configurations n k).filter (bad k gap q)).card

/-- A finite, exact worst-case numerator, rather than a security hypothesis. -/
def maxBadCount (n k gap : Nat) : Nat :=
  Finset.univ.sup (badCount n k gap)

def errorBound (n k gap : Nat) : ℝ≥0∞ :=
  (maxBadCount n k gap : ℝ≥0∞) / ((configurations n k).card : ℝ≥0∞)

theorem errorBound_formula (n k gap : Nat) :
    errorBound n k gap = (maxBadCount n k gap : ℝ≥0∞) / (2^n * Nat.choose n k : ℝ≥0∞) := by
  unfold errorBound
  rw [configurations_card]
  norm_cast

theorem probability_count (n k gap : Nat) (hk : k ≤ n) (q : Pattern n) :
    eventProb (distribution n k hk) (bad k gap q) =
      (badCount n k gap q : ℝ≥0∞) / ((configurations n k).card : ℝ≥0∞) := by
  unfold eventProb distribution
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, badCount]

theorem classical (n k gap : Nat) (hk : k ≤ n) (q : Pattern n) :
    eventProb (distribution n k hk) (bad k gap q) ≤ errorBound n k gap := by
  rw [probability_count]
  apply ENNReal.div_le_div_right
  exact_mod_cast (Finset.le_sup (f := badCount n k gap) (Finset.mem_univ q))

theorem errorBound_le_one (n k gap : Nat) : errorBound n k gap ≤ 1 := by
  have h : maxBadCount n k gap ≤ (configurations n k).card := by
    apply Finset.sup_le
    intro q _
    exact Finset.card_filter_le _ _
  unfold errorBound
  have hh : (maxBadCount n k gap : ℝ≥0∞) ≤ ((configurations n k).card : ℝ≥0∞) := by exact_mod_cast h
  exact (ENNReal.div_le_div_right hh _).trans ENNReal.div_self_le_one

theorem errorBound_finite (n k gap : Nat) : errorBound n k gap ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (errorBound_le_one n k gap)

theorem independent (n k : Nat) (hk : k ≤ n) :
    distribution n k hk =
      (uniform (Fin n → Fin 2)).bind (fun s =>
        (Sampling.sample (Finset.univ : Finset (Fin n)) k (by simpa using hk)).map (fun T => (s,T))) := by
  ext c
  have hm (s : Fin n → Fin 2) :
      ((Sampling.sample (Finset.univ : Finset (Fin n)) k (by simpa using hk)).map (fun T => (s,T))) c =
        if s = c.1 then Sampling.sample (Finset.univ : Finset (Fin n)) k (by simpa using hk) c.2 else 0 := by
    rw [PMF.map_apply, tsum_eq_single c.2]
    · by_cases h : s = c.1
      · have hc : c = (s,c.2) := Prod.ext h.symm rfl
        rw [if_pos hc, if_pos h]
      · have hc : c ≠ (s,c.2) := fun he => h (congrArg Prod.fst he).symm
        rw [if_neg hc, if_neg h]
    · intro T hT
      have h : c ≠ (s,T) := by intro he; exact hT (congrArg Prod.snd he).symm
      simp [h]
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [hm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [distribution, PMF.uniformOfFinset_apply, configurations, uniform,
    PMF.uniformOfFintype_apply, Sampling.sample]
  by_cases h : c.2 ∈ Finset.univ.powersetCard k <;> simp [h, ENNReal.mul_inv]

end
end Foundation.Quantum.QKD.PairwiseSampling
