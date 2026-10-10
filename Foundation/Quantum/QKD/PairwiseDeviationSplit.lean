import Foundation.Quantum.QKD.PairwiseWeightDeviation

/-! Integer-scaled decomposition of the actual fixed-size pairwise sampling
event. The selector marginal is the original uniform seed. Only the first
component is bounded analytically here; sampling without replacement remains
an explicit event, rather than being assumed independent or with replacement. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def sampleDifference {n : Nat} (k : Nat) (q : Pattern n) (c : Configuration n) : ℝ :=
  n * (tested q c : ℝ) - k * (selectedWeight q c.1 : ℝ)

theorem deviation_split {n : Nat} (k : Nat) (q : Pattern n) (c : Configuration n) :
    (n * (tested q c : ℝ) - k * (remaining q c.1 : ℝ)) =
      sampleDifference k q c + k * weightDifference q c.1 := by
  rw [weightDifference_counts]
  unfold sampleDifference
  ring

theorem natdist_real (a b : Nat) : (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  by_cases h : a ≤ b
  · have hr : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hr)]
    ring
  · have hh : b ≤ a := by omega
    have hr : (b : ℝ) ≤ a := by exact_mod_cast hh
    rw [Nat.dist_eq_sub_of_le_right hh, Nat.cast_sub hh, abs_of_nonneg (sub_nonneg.mpr hr)]

theorem bad_split {n : Nat} (k gap : Nat) (q : Pattern n) (c : Configuration n)
    (u t : ℝ) (hgap : u + k*t ≤ gap) (hbad : bad k gap q c) :
    u < |sampleDifference k q c| ∨ t < |weightDifference q c.1| := by
  unfold bad at hbad
  have hb : (gap : ℝ) < (Nat.dist (n * tested q c) (k * remaining q c.1) : ℝ) := by
    exact_mod_cast hbad
  rw [natdist_real, Nat.cast_mul, Nat.cast_mul, deviation_split] at hb
  by_contra h
  push Not at h
  have ha : |sampleDifference k q c + (k : ℝ)*weightDifference q c.1| ≤
      |sampleDifference k q c| + (k : ℝ)*|weightDifference q c.1| := by
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] using
      abs_add_le (sampleDifference k q c) ((k : ℝ)*weightDifference q c.1)
  have hm := mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith [h.1]

theorem selector_distribution (n k : Nat) (hk : k ≤ n) :
    (distribution n k hk).map Prod.fst = uniform (Fin n → Fin 2) := by
  rw [independent, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have h (s : Fin n → Fin 2) :
      PMF.map (fun _ : Finset (Fin n) => s)
        (Sampling.sample (Finset.univ : Finset (Fin n)) k (by simpa using hk)) = PMF.pure s :=
    PMF.map_const _ s
  simp_rw [h]
  exact PMF.bind_pure _

theorem selector_event {n : Nat} (k : Nat) (hk : k ≤ n)
    (P : (Fin n → Fin 2) → Prop) [DecidablePred P] :
    eventProb (distribution n k hk) (fun c => P c.1) = eventProb (uniform (Fin n → Fin 2)) P := by
  have h := congrArg (fun p => eventProb p P) (selector_distribution n k hk)
  unfold eventProb at h
  rw [PMF.toOuterMeasure_map_apply] at h
  exact h

/-- The full event uses the actual distribution and without-replacement test.
The second event still needs its own concentration proof. -/
theorem classical_decomposition_bound {n : Nat} (k gap : Nat) (hk : k ≤ n)
    (q : Pattern n) (u t : ℝ) (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    (eventProb (distribution n k hk) (bad k gap q)).toReal ≤
      n / t^2 + (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal := by
  classical
  have hunion : (eventProb (distribution n k hk) (bad k gap q)).toReal ≤
      (eventProb (distribution n k hk) (fun c => t < |weightDifference q c.1|)).toReal +
      (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal := by
    rw [eventProb_toReal, eventProb_toReal, eventProb_toReal, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    by_cases hb : bad k gap q c
    · have hs := bad_split k gap q c u t hgap hb
      rcases hs with hs | hs
      · simp only [hb, hs, ite_true]
        split_ifs <;> linarith [show 0 ≤ (distribution n k hk c).toReal from ENNReal.toReal_nonneg]
      · simp only [hb, hs, ite_true]
        split_ifs <;> linarith [show 0 ≤ (distribution n k hk c).toReal from ENNReal.toReal_nonneg]
    · simp only [hb, ite_false]
      positivity
  rw [selector_event k hk (fun s => t < |weightDifference q s|)] at hunion
  linarith [weightDifference_tail q t ht]

end
end Foundation.Quantum.QKD.PairwiseSampling
