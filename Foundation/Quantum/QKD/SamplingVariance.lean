import Foundation.Quantum.QKD.SamplingMoments

/-! Exact finite-population variance of the integer-scaled test deviation.
All error sets are fixed arbitrarily; no independence of errors is assumed. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

def centered {n : Nat} (k : Nat) (E T : Finset (Fin n)) : ℝ :=
  n * hits E T - k * E.card

theorem centered_second_moment {n : Nat} (hn : 2 ≤ n) (k : Nat) (hk : k ≤ n)
    (E : Finset (Fin n)) :
    expectation (fullSample n k hk) (fun T => centered k E T ^ 2) =
      (k : ℝ)*(n-k)/(n-1) * E.card * ((n : ℝ)-E.card) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he : (fun T : Finset (Fin n) => centered k E T ^ 2) =
      (fun T => hits E T ^ 2 * (n : ℝ)^2 - hits E T * (2*(n : ℝ)*k*E.card) + ((k : ℝ)*E.card)^2) := by
    funext T
    unfold centered
    ring
  rw [he, expectation_add, expectation_sub, expectation_mul_const, expectation_mul_const,
    expectation_const, hits_second_moment, hits_mean]
  field_simp
  ring

theorem centered_second_moment_le {n : Nat} (hn : 2 ≤ n) (k : Nat) (hk : k ≤ n)
    (E : Finset (Fin n)) :
    expectation (fullSample n k hk) (fun T => centered k E T ^ 2) ≤ (k : ℝ)*n^2/4 := by
  rw [centered_second_moment hn k hk]
  by_cases hk0 : k = 0
  · subst k
    simp
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hn1 : (0 : ℝ) < n-1 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hw : (E.card : ℝ) ≤ n := by
    have h : E.card ≤ n := by simpa using Finset.card_le_univ E
    exact_mod_cast h
  have hw0 : (0 : ℝ) ≤ E.card := by positivity
  have hc0 : (0 : ℝ) ≤ (k : ℝ)*(n-k)/(n-1) := by positivity
  have hc : (k : ℝ)*(n-k)/(n-1) ≤ k := by
    apply (div_le_iff₀ hn1).mpr
    nlinarith
  have hv : (E.card : ℝ)*((n : ℝ)-E.card) ≤ (n : ℝ)^2/4 := by
    nlinarith [sq_nonneg ((E.card : ℝ)-(n : ℝ)/2)]
  calc
    _ = ((k : ℝ)*(n-k)/(n-1)) * ((E.card : ℝ)*((n : ℝ)-E.card)) := by ring
    _ ≤ ((k : ℝ)*(n-k)/(n-1)) * ((n : ℝ)^2/4) := mul_le_mul_of_nonneg_left hv hc0
    _ ≤ (k : ℝ) * ((n : ℝ)^2/4) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- The entire zero/one-position cases vanish, rather than dividing by n-1. -/
theorem centered_small {n : Nat} (hn : n < 2) (k : Nat) (hk : k ≤ n)
    (E T : Finset (Fin n)) (hT : T.card = k) : centered k E T = 0 := by
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · have hE : E = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ => Fin.elim0 i)
    simp [centered, hits, hE]
  · by_cases hk0 : k = 0
    · have hTE : T = ∅ := Finset.card_eq_zero.mp (hT.trans hk0)
      simp [centered, hits, indicator, hk0, hTE]
    · have hk1 : k = 1 := by omega
      have hTU : T = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa [hk1] using hT
      simp only [centered, hits_card, hTU, Finset.inter_univ, hk1, Nat.cast_one, one_mul, sub_self]

/-- Strict deviation event under the actual fixed-size PMF. -/
theorem centered_tail {n : Nat} (hn : 2 ≤ n) (k : Nat) (hk : k ≤ n)
    (E : Finset (Fin n)) (u : ℝ) (hu : 0 < u) :
    (Foundation.Probability.eventProb (fullSample n k hk) (fun T => u < |centered k E T|)).toReal ≤
      (k : ℝ)*n^2/(4*u^2) := by
  classical
  have ht : u^2 * (Foundation.Probability.eventProb (fullSample n k hk)
      (fun T => u < |centered k E T|)).toReal ≤
      expectation (fullSample n k hk) (fun T => centered k E T ^ 2) := by
    rw [eventProb_toReal, Finset.mul_sum]
    unfold expectation
    apply Finset.sum_le_sum
    intro T _
    by_cases hT : u < |centered k E T|
    · simp only [hT, ite_true]
      have hsq : u^2 ≤ centered k E T ^ 2 := by
        nlinarith [sq_abs (centered k E T), abs_nonneg (centered k E T)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq
        (show 0 ≤ (fullSample n k hk T).toReal from ENNReal.toReal_nonneg)
    · simp only [hT, ite_false, mul_zero]
      positivity
  have h := ht.trans (centered_second_moment_le hn k hk E)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*u^2)).mpr
  nlinarith

theorem fullSample_of_card_ne {n : Nat} (k : Nat) (hk : k ≤ n) (T : Finset (Fin n))
    (hT : T.card ≠ k) : fullSample n k hk T = 0 := by
  unfold fullSample sample
  apply PMF.uniformOfFinset_apply_of_notMem
  intro h
  exact hT (Finset.mem_powersetCard.mp h).2

theorem centered_tail_small {n : Nat} (hn : n < 2) (k : Nat) (hk : k ≤ n)
    (E : Finset (Fin n)) (u : ℝ) (hu : 0 < u) :
    (Foundation.Probability.eventProb (fullSample n k hk) (fun T => u < |centered k E T|)).toReal = 0 := by
  classical
  rw [eventProb_toReal]
  apply Finset.sum_eq_zero
  intro T _
  by_cases hT : T.card = k
  · rw [centered_small hn k hk E T hT]
    simp [hu.le]
  · simp [fullSample_of_card_ne k hk T hT]

/-- All dimensions and sample sizes, including n=0, n=1 and k=0. -/
theorem centered_tail_all {n : Nat} (k : Nat) (hk : k ≤ n)
    (E : Finset (Fin n)) (u : ℝ) (hu : 0 < u) :
    (Foundation.Probability.eventProb (fullSample n k hk) (fun T => u < |centered k E T|)).toReal ≤
      (k : ℝ)*n^2/(4*u^2) := by
  by_cases hn : 2 ≤ n
  · exact centered_tail hn k hk E u hu
  · rw [centered_tail_small (by omega) k hk E u hu]
    positivity

end
end Foundation.Quantum.QKD.Sampling
