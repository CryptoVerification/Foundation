import Foundation.Quantum.QKD.SamplingVariance
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Bernoulli-selection foundations for exponential sampling bounds.

This module proves the scalar Hoeffding lemma and the normalization and
moment-generating-function factorization of independent subset selection.
These are preparatory results: conditioning on a fixed sample size and
bounding the deviation under `Sampling.fullSample` remain to be proved. -/

namespace Foundation.Quantum.QKD.Bernoulli
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-! ### Hoeffding's lemma for a single bounded indicator -/

/-- A twice differentiable function with nonpositive second derivative, zero
value and zero derivative at the origin is nonpositive. -/
private theorem nonpos_of_second_deriv_nonpos {f : ℝ → ℝ} (hf : ∀ x, deriv (deriv f) x ≤ 0)
    (hfd : Differentiable ℝ f) (hfdd : Differentiable ℝ (deriv f)) (hf0 : f 0 = 0)
    (hfd0 : deriv f 0 = 0) (t : ℝ) : f t ≤ 0 := by
  have hanti : Antitone (deriv f) := antitone_of_deriv_nonpos hfdd hf
  have hcont : ContinuousOn f Set.univ := hfd.continuous.continuousOn
  rcases lt_or_ge t 0 with ht | ht
  · obtain ⟨c, hcm, hc⟩ : ∃ c ∈ Set.Ioo t 0, deriv f c = (f 0 - f t) / (0 - t) :=
      exists_deriv_eq_slope f (by linarith) (hcont.mono (Set.subset_univ _))
        (fun x _ => (hfd x).differentiableWithinAt)
    have hne : (0:ℝ) - t ≠ 0 := by linarith
    have h1 : f 0 - f t = deriv f c * (0 - t) := by
      rw [hc, div_mul_cancel₀ _ hne]
    have h2 : (0:ℝ) ≤ deriv f c := by
      have h3 : deriv f 0 ≤ deriv f c := hanti hcm.2.le
      rw [hfd0] at h3; exact h3
    have h4 : (0:ℝ) ≤ deriv f c * (0 - t) := mul_nonneg h2 (by linarith)
    linarith [hf0]
  · rcases eq_or_lt_of_le ht with ht | ht
    · subst ht; linarith [hf0]
    · obtain ⟨c, hcm, hc⟩ : ∃ c ∈ Set.Ioo 0 t, deriv f c = (f t - f 0) / (t - 0) :=
        exists_deriv_eq_slope f (by linarith) (hcont.mono (Set.subset_univ _))
          (fun x _ => (hfd x).differentiableWithinAt)
      have hne : (t:ℝ) - 0 ≠ 0 := by linarith
      have h1 : f t - f 0 = deriv f c * (t - 0) := by
        rw [hc, div_mul_cancel₀ _ hne]
      have h2 : deriv f c ≤ 0 := by
        have h3 : deriv f c ≤ deriv f 0 := hanti hcm.1.le
        rw [hfd0] at h3; exact h3
      have h4 : deriv f c * (t - 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 (by linarith)
      linarith [hf0]

/-- The centered logarithmic mgf of a Bernoulli variable with mean `p`. -/
private def bernoulliLogMgf (p : ℝ) : ℝ → ℝ :=
  fun s => Real.log (1 - p + p * Real.exp s) - p * s

private theorem bernoulliLogMgf_arg_pos (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (0:ℝ) < 1 - p + p * Real.exp t := by
  by_cases h : p = 1
  · subst h; simpa using Real.exp_pos t
  · have h1 : (0:ℝ) < 1 - p := by
      by_contra hc; push Not at hc; exact h (by linarith)
    have h2 : 0 ≤ p * Real.exp t := by positivity
    linarith

private theorem hasDerivAt_bernoulliLogMgf (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    HasDerivAt (bernoulliLogMgf p) (p * Real.exp t / (1 - p + p * Real.exp t) - p) t := by
  have hD : 1 - p + p * Real.exp t ≠ 0 := (bernoulliLogMgf_arg_pos p hp0 hp1 t).ne'
  have hci : HasDerivAt (fun s : ℝ => p * s) p t := by
    have hend := (hasDerivAt_id t).const_mul p
    simpa using hend
  have hraw := ((Real.hasDerivAt_log hD).comp t ((Real.hasDerivAt_exp t).const_mul p
    |>.const_add (1 - p))).sub hci
  have heq0 : bernoulliLogMgf p
      = (Real.log ∘ fun x : ℝ => 1 - p + p * Real.exp x) - fun s => p * s := rfl
  have heq1 : (1 - p + p * Real.exp t)⁻¹ * (p * Real.exp t) - p
      = p * Real.exp t / (1 - p + p * Real.exp t) - p := by field_simp
  rw [heq0]
  exact heq1 ▸ hraw

private theorem deriv_bernoulliLogMgf_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    deriv (bernoulliLogMgf p)
      = fun s => p * Real.exp s / (1 - p + p * Real.exp s) - p :=
  funext fun s => (hasDerivAt_bernoulliLogMgf p hp0 hp1 s).deriv

private theorem hasDerivAt_deriv_bernoulliLogMgf (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    HasDerivAt (deriv (bernoulliLogMgf p))
      (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2) t := by
  have hD : 1 - p + p * Real.exp t ≠ 0 := (bernoulliLogMgf_arg_pos p hp0 hp1 t).ne'
  have hnum : HasDerivAt (fun u : ℝ => p * Real.exp u) (p * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul p
  have hden : HasDerivAt (fun u : ℝ => 1 - p + p * Real.exp u) (p * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul p |>.const_add (1 - p)
  have hsub := (HasDerivAt.div hnum hden hD).sub (hasDerivAt_const (c := p) (x := t))
  have hkey : p * Real.exp t * (1 - p + p * Real.exp t) - p * Real.exp t * (p * Real.exp t)
      = p * (1 - p) * Real.exp t := by ring
  have heq : (fun s : ℝ => p * Real.exp s / (1 - p + p * Real.exp s) - p)
      = ((fun u : ℝ => p * Real.exp u) / fun u : ℝ => 1 - p + p * Real.exp u) - fun x => p := rfl
  rw [← heq, sub_zero, hkey] at hsub
  rw [deriv_bernoulliLogMgf_eq p hp0 hp1]
  exact hsub

private theorem deriv_deriv_bernoulliLogMgf_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    deriv (deriv (bernoulliLogMgf p)) t ≤ 1 / 4 := by
  rw [(hasDerivAt_deriv_bernoulliLogMgf p hp0 hp1 t).deriv]
  have hpos : (0:ℝ) < (1 - p + p * Real.exp t) ^ 2 := by
    have := bernoulliLogMgf_arg_pos p hp0 hp1 t; positivity
  rw [div_le_iff₀ hpos]
  have h4 : 4 * (p * (1 - p) * Real.exp t) ≤ (1 - p + p * Real.exp t) ^ 2 := by
    have h1 : 0 ≤ ((1:ℝ) - p - p * Real.exp t) ^ 2 := sq_nonneg _
    have h2 : (1 - p + p * Real.exp t) ^ 2 - 4 * (p * (1 - p) * Real.exp t)
        = ((1:ℝ) - p - p * Real.exp t) ^ 2 := by ring
    linarith
  linarith

/-- `8 * log-mgf - s ^ 2`; its second derivative is nonpositive by the bound
above, and it vanishes together with its derivative at the origin. -/
private def hoeffdingDeficit (p : ℝ) : ℝ → ℝ := fun s => 8 * bernoulliLogMgf p s - s ^ 2

private theorem hasDerivAt_hoeffdingDeficit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    HasDerivAt (hoeffdingDeficit p)
      (8 * (p * Real.exp t / (1 - p + p * Real.exp t) - p) - 2 * t) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    have := hasDerivAt_pow 2 t
    simpa using this
  exact ((hasDerivAt_bernoulliLogMgf p hp0 hp1 t).const_mul 8).sub h2

private theorem hasDerivAt_deriv_hoeffdingDeficit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    HasDerivAt (deriv (hoeffdingDeficit p))
      (8 * (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2) - 2) t := by
  have hA0 := hasDerivAt_deriv_bernoulliLogMgf p hp0 hp1 t
  rw [deriv_bernoulliLogMgf_eq p hp0 hp1] at hA0
  have hA : HasDerivAt (fun s : ℝ => p * Real.exp s / (1 - p + p * Real.exp s) - p)
      (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2) t := hA0
  have hB : HasDerivAt (fun s : ℝ => 8 * (p * Real.exp s / (1 - p + p * Real.exp s) - p))
      (8 * (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2)) t := hA.const_mul 8
  have hC : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    have hend := (hasDerivAt_id t).const_mul 2
    simpa using hend
  have hfirst : deriv (hoeffdingDeficit p)
      = fun s => 8 * (p * Real.exp s / (1 - p + p * Real.exp s) - p) - 2 * s :=
    funext fun s => (hasDerivAt_hoeffdingDeficit p hp0 hp1 s).deriv
  have heq : (fun s : ℝ => 8 * (p * Real.exp s / (1 - p + p * Real.exp s) - p) - 2 * s)
      = (fun s : ℝ => 8 * (p * Real.exp s / (1 - p + p * Real.exp s) - p))
        - (fun s : ℝ => 2 * s) := rfl
  rw [hfirst, heq]
  exact hB.sub hC

private theorem hoeffdingDeficit_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hoeffdingDeficit p t ≤ 0 := by
  have hfdd : ∀ x, HasDerivAt (deriv (hoeffdingDeficit p))
      (8 * (p * (1 - p) * Real.exp x / (1 - p + p * Real.exp x) ^ 2) - 2) x :=
    fun x => hasDerivAt_deriv_hoeffdingDeficit p hp0 hp1 x
  refine nonpos_of_second_deriv_nonpos (f := hoeffdingDeficit p) ?_ ?_ ?_ ?_ ?_ t
  · intro x
    have hstep := deriv_deriv_bernoulliLogMgf_le p hp0 hp1 x
    rw [(hasDerivAt_deriv_bernoulliLogMgf p hp0 hp1 x).deriv] at hstep
    rw [(hfdd x).deriv]
    linarith
  · intro x; exact (hasDerivAt_hoeffdingDeficit p hp0 hp1 x).differentiableAt
  · intro x; exact (hfdd x).differentiableAt
  · simp [hoeffdingDeficit, bernoulliLogMgf, Real.log_one]
  · rw [(hasDerivAt_hoeffdingDeficit p hp0 hp1 0).deriv]
    simp [Real.exp_zero]

/-- The centered moment-generating function of a Bernoulli variable with
mean `p ∈ [0, 1]` is bounded by `exp (t² / 8)` for every real `t`. -/
theorem hoeffding_lemma (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-(p * t)) + p * Real.exp ((1 - p) * t) ≤ Real.exp (t ^ 2 / 8) := by
  have hex : (1 - p) * Real.exp (-(p * t)) + p * Real.exp ((1 - p) * t)
      = Real.exp (bernoulliLogMgf p t) := by
    have hkey : Real.exp (-(p * t)) * Real.exp t = Real.exp ((1 - p) * t) := by
      rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
    have hprot : Real.exp (-(p * t)) * (1 - p + p * Real.exp t)
        = (1 - p) * Real.exp (-(p * t)) + p * Real.exp ((1 - p) * t) := by
      rw [mul_add]
      congr 1
      · ring
      · rw [mul_left_comm, hkey]
    rw [← hprot, ← Real.exp_log (bernoulliLogMgf_arg_pos p hp0 hp1 t), ← Real.exp_add]
    congr 1
    simp only [bernoulliLogMgf, sub_eq_add_neg]
    ring
  rw [hex, Real.exp_le_exp]
  have hdef : 8 * bernoulliLogMgf p t - t ^ 2 ≤ 0 := hoeffdingDeficit_le p t hp0 hp1
  linarith

/-! ### Product Bernoulli selection -/

/-- Weight of a selected subset when each position is independently selected
with probability `q`. -/
def bernoulliWeight (q : ℝ) {n : ℕ} (s : Finset (Fin n)) : ℝ :=
  q ^ s.card * (1 - q) ^ (n - s.card)

/-- In the probability-parameter range all subset weights are nonnegative. -/
theorem bernoulliWeight_nonneg (q : ℝ) {n : ℕ} (s : Finset (Fin n))
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ bernoulliWeight q s := by
  unfold bernoulliWeight
  exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)

/-- The Bernoulli weight is the product of the local inclusion/exclusion
weights. -/
theorem bernoulliWeight_factors (q : ℝ) {n : ℕ} (s : Finset (Fin n)) :
    bernoulliWeight q s =
      (∏ _i ∈ s, q) * ∏ _i ∈ (Finset.univ : Finset (Fin n)) \ s, (1 - q) := by
  have hcard : ((Finset.univ : Finset (Fin n)) \ s).card = n - s.card := by
    simp [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
  simp [bernoulliWeight, Finset.prod_const, hcard]

/-- The Bernoulli subset weights sum to one. -/
theorem bernoulliWeight_sum (q : ℝ) {n : ℕ} :
    (∑ s : Finset (Fin n), bernoulliWeight q s) = 1 := by
  have hpu : (Finset.univ : Finset (Fin n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))) := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin n), bernoulliWeight q s) =
        ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ t, q) * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, (1 - q) := by
      rw [hpu]
      apply Finset.sum_congr rfl
      intro t _
      exact bernoulliWeight_factors q t
    _ = ∏ i : Fin n, (q + (1 - q)) := by
      symm
      exact Finset.prod_add (fun _ : Fin n => q) (fun _ => 1 - q) Finset.univ
    _ = 1 := by simp

/-- The moment-generating sum for errors in `E` factors over positions. -/
theorem bernoulliWeight_mgf (q θ : ℝ) {n : ℕ} (E : Finset (Fin n)) :
    (∑ s : Finset (Fin n), bernoulliWeight q s *
      Real.exp (θ * (Foundation.Quantum.QKD.Sampling.hits E s : ℝ))) =
      (1 - q + q * Real.exp θ) ^ E.card := by
  have hpu : (Finset.univ : Finset (Fin n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))) := by
    ext s
    simp
  let f : Fin n → ℝ := fun i => q * (if i ∈ E then Real.exp θ else 1)
  let g : Fin n → ℝ := fun _ => 1 - q
  have hprod : (∏ i : Fin n, (f i + g i)) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ t, f i) * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, g i :=
    Finset.prod_add f g Finset.univ
  have hterms (t : Finset (Fin n)) :
      bernoulliWeight q t * Real.exp (θ * (Foundation.Quantum.QKD.Sampling.hits E t : ℝ)) =
        (∏ i ∈ t, f i) * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, g i := by
    classical
    rw [bernoulliWeight_factors]
    simp only [f, g, Finset.prod_mul_distrib]
    rw [Foundation.Quantum.QKD.Sampling.hits_card]
    simp only [Finset.prod_ite_mem, Finset.prod_const, Finset.card_sdiff, Finset.card_univ,
      Fintype.card_fin]
    rw [← Real.exp_nat_mul]
    simp [Finset.inter_comm, Finset.inter_univ, mul_comm, mul_left_comm, mul_assoc]
  calc
    (∑ s : Finset (Fin n), bernoulliWeight q s *
        Real.exp (θ * (Foundation.Quantum.QKD.Sampling.hits E s : ℝ))) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ t, f i) * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, g i := by
          rw [hpu]
          apply Finset.sum_congr rfl
          intro t _
          exact hterms t
    _ = ∏ i : Fin n, (f i + g i) := hprod.symm
    _ = (1 - q + q * Real.exp θ) ^ E.card := by
      simp only [f, g]
      have hpoint (i : Fin n) :
          q * (if i ∈ E then Real.exp θ else 1) + (1 - q) =
            if i ∈ E then 1 - q + q * Real.exp θ else 1 := by
        by_cases hi : i ∈ E
        · simp only [if_pos hi]
          ring
        · simp [hi]
      simp_rw [hpoint]
      rw [Finset.prod_ite]
      simp [Finset.prod_const]

end
end Foundation.Quantum.QKD.Bernoulli
