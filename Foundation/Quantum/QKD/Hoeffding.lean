import Foundation.Quantum.QKD.PairwiseWeightDeviation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Hoeffding-type concentration for the uniform product distribution over
`Fin n → Fin 2`. The two ingredients are the analytic core `cosh x ≤ exp
(x²/2)` and the coordinate factorization of the moment generating function.
No independence in the error pattern is assumed: only the protocol's
independent uniform two-choice seed is used. -/
namespace Foundation.Quantum.QKD.Hoeffding
noncomputable section
open Foundation.Probability
open Foundation.Quantum.QKD.PairwiseSampling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Splitting a sum over `Fin (n+1) → Fin 2` by the newest coordinate. -/
theorem sum_cons (n : ℕ) (g : (Fin (n + 1) → Fin 2) → ℝ) :
    ∑ s : Fin (n + 1) → Fin 2, g s = ∑ s' : Fin n → Fin 2, ∑ b : Fin 2, g (Fin.cons b s') := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin 2))
    (fun p => g (Fin.cons p.1 p.2)) g (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type_right]

/-- The analytic core, stated without naming `cosh`. -/
theorem exp_pair_le {a : ℝ} :
    Real.exp a + Real.exp (-a) ≤ 2 * Real.exp (a ^ 2 / 2) := by
  have hcosh : (2:ℝ) * Real.cosh a = Real.exp a + Real.exp (-a) := by
    have e1 : ((Complex.exp (a:ℂ)).re : ℝ) = Real.exp a := by
      simp [Complex.exp_re]
    have e2 : ((Complex.exp (-(a:ℂ))).re : ℝ) = Real.exp (-a) := by
      simp [Complex.exp_re]
    rw [Real.cosh, ← Complex.re_ofReal_mul]
    push_cast
    rw [Complex.two_cosh, Complex.add_re, e1, e2]
  rw [← hcosh]
  exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq a) (by norm_num)


/-- Splitting a sum over `Fin (n+1)` off the youngest index. The `m` argument
keeps the rewrite pattern rigid, so it never matches sums over other indices. -/
theorem sum_fin_succ {α} [AddCommMonoid α] (m : ℕ) {f : Fin (m + 1) → α} :
    ∑ i : Fin (m + 1), f i = f 0 + ∑ i : Fin m, f i.succ := Fin.sum_univ_succ f

/-- Splitting a sum over `Fin 2`; the index type is a literal, so the pattern
is rigid as well. -/
theorem sum_fin_two {α} [AddCommMonoid α] {f : Fin 2 → α} :
    ∑ i : Fin 2, f i = f 0 + f 1 := by
  rw [sum_fin_succ 1, Fin.sum_univ_one]
  rfl


/-- Splitting a product over `Fin (n+1)` off the youngest index. -/
theorem prod_fin_split (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, f i.succ := Fin.prod_univ_succ f


/-- The inner sum over `Fin (n+1)` splits off the youngest index. Stated with
the ascribed cons form, which is the only position where `Fin.cons` elaborates. -/
theorem sum_cons_inner (n : ℕ) (a : Fin (n + 1) → Fin 2 → ℝ) (b : Fin 2)
    (s' : Fin n → Fin 2) :
    ∑ i : Fin (n + 1), a i ((Fin.cons b s' : Fin (n + 1) → Fin 2) i)
      = a 0 b + ∑ i : Fin n, a i.succ (s' i) := by
  have hS : ∑ i : Fin (n + 1), a i ((Fin.cons b s' : Fin (n + 1) → Fin 2) i)
      = a 0 ((Fin.cons b s' : Fin (n + 1) → Fin 2) 0)
        + ∑ i : Fin n, a i.succ ((Fin.cons b s' : Fin (n + 1) → Fin 2) i.succ) :=
    Fin.sum_univ_succ (fun i => a i ((Fin.cons b s' : Fin (n + 1) → Fin 2) i))
  rw [hS]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The signed bits are coefficients of the two coordinate values. -/
def coeff {n : ℕ} (q : Pattern n) : Fin n → Fin 2 → ℝ :=
  fun i b => (q (i, b)).val - (q (i, flip b)).val

theorem signedBit_coeff {n : ℕ} (q : Pattern n) (s : Fin n → Fin 2) (i : Fin n) :
    signedBit q s i = coeff q i (s i) := rfl

theorem coeff_flip {n : ℕ} (q : Pattern n) (i : Fin n) : coeff q i 1 = -coeff q i 0 := by
  have h1 : (flip 1 : Fin 2) = 0 := by decide
  have h0 : (flip 0 : Fin 2) = 1 := by decide
  unfold coeff
  rw [h1, h0]
  ring

theorem coeff_sq_le_one {n : ℕ} (q : Pattern n) (i : Fin n) (b : Fin 2) :
    coeff q i b ^ 2 ≤ 1 := by
  have h := signedBit_sq_le_one (n := n) q (Function.update (fun _ => (0:Fin 2)) i b) i
  rw [signedBit_coeff] at h
  simpa using h

theorem weightDifference_eq_sum {n : ℕ} (q : Pattern n) (s : Fin n → Fin 2) :
    weightDifference q s = ∑ i, coeff q i (s i) := by
  unfold weightDifference
  exact Finset.sum_congr rfl (fun i _ => signedBit_coeff q s i)





/-- The moment generating function factorizes over the coordinates. -/
theorem mgf_factor (n : ℕ) (a : Fin n → Fin 2 → ℝ) (r : ℝ) :
    ∑ s : Fin n → Fin 2, Real.exp (r * ∑ i, a i (s i))
      = ∏ i, (Real.exp (r * a i 0) + Real.exp (r * a i 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hb (T : ℝ) : ∑ b : Fin 2, Real.exp (r * (a 0 b + T))
          = Real.exp (r * (a 0 0 + T)) + Real.exp (r * (a 0 1 + T)) := by
        rw [Fin.sum_univ_two]
      rw [sum_cons n (fun s => Real.exp (r * ∑ i, a i (s i)))]
      have key : ∀ s' : Fin n → Fin 2,
          ∑ b : Fin 2, Real.exp (r * ∑ i : Fin (n + 1), a i ((Fin.cons b s' : Fin (n + 1) → Fin 2) i))
            = Real.exp (r * (a 0 0 + ∑ i : Fin n, a (i.succ) (s' i)))
              + Real.exp (r * (a 0 1 + ∑ i : Fin n, a (i.succ) (s' i))) := by
        intro s'
        simp only [sum_cons_inner n a, sum_fin_two]
      rw [Finset.sum_congr rfl (fun s' _ => key s')]
      have alg : ∀ s' : Fin n → Fin 2,
          Real.exp (r * (a 0 0 + ∑ i : Fin n, a (i.succ) (s' i)))
            + Real.exp (r * (a 0 1 + ∑ i : Fin n, a (i.succ) (s' i)))
            = Real.exp (r * ∑ i : Fin n, a (i.succ) (s' i))
                * (Real.exp (r * a 0 0) + Real.exp (r * a 0 1)) := by
        intro s'
        rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
        ring
      rw [Finset.sum_congr rfl (fun s' _ => alg s'), ← Finset.sum_mul]
      rw [ih ((fun i : Fin n => a (i.succ)) : Fin n → Fin 2 → ℝ)]
      rw [Fin.prod_univ_succ]
      ring

/-- The moment generating function of the weight difference. -/
theorem mgf_weighted_le {n : ℕ} (q : Pattern n) (r : ℝ) :
    ∑ s : Fin n → Fin 2, Real.exp (r * weightDifference q s) ≤
      (2 : ℝ) ^ n * Real.exp (r ^ 2 * n / 2) := by
  have h1 : ∑ s : Fin n → Fin 2, Real.exp (r * weightDifference q s)
      = ∑ s : Fin n → Fin 2, Real.exp (r * ∑ i, coeff q i (s i)) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [weightDifference_eq_sum]
  rw [h1, mgf_factor n (coeff q) r]
  have h2 (i : Fin n) :
      Real.exp (r * coeff q i 0) + Real.exp (r * coeff q i 1)
        ≤ (2:ℝ) * Real.exp ((r * coeff q i 0) ^ 2 / 2) := by
    rw [coeff_flip, mul_neg]
    exact exp_pair_le (a := r * coeff q i 0)
  have hmag (i : Fin n) : (r * coeff q i 0) ^ 2 / 2 ≤ r ^ 2 / 2 := by
    have h := coeff_sq_le_one q i 0
    nlinarith [sq_nonneg (coeff q i 0), sq_nonneg r]
  have h3 : ∏ i : Fin n, (Real.exp (r * coeff q i 0) + Real.exp (r * coeff q i 1))
      ≤ ∏ i : Fin n, (2:ℝ) * Real.exp (r ^ 2 / 2) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ =>
      (h2 i).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmag i)) (by positivity)))
  calc ∏ i : Fin n, (Real.exp (r * coeff q i 0) + Real.exp (r * coeff q i 1))
      ≤ ∏ i : Fin n, (2:ℝ) * Real.exp (r ^ 2 / 2) := h3
    _ = (2:ℝ) ^ n * Real.exp (r ^ 2 * n / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        ring_nf

/- NOTE (work in progress): the final tail bound `weightDifference_tail_exp`
is the remaining step. Its ingredients are all present above: `exp_pair_le`
(the Hoeffding lemma core), `mgf_weighted_le` (the moment generating bound) and
the Markov argument. -/

/-- The exponential concentration bound for the selector weight difference.
This replaces the polynomial Chebyshev bound on the first component of the
Bouman-Fehr sampling error. -/
theorem weightDifference_tail_exp {n : ℕ} (q : Pattern n) (u : ℝ) (hu : 0 < u) (hn : 0 < n) :
    (eventProb (uniform (Fin n → Fin 2)) (fun s => u < |weightDifference q s|)).toReal ≤
      2 * Real.exp (-(u ^ 2) / (2 * n)) := by
  have hprob (s : Fin n → Fin 2) :
      (uniform (Fin n → Fin 2) s).toReal = (1:ℝ) / (2 ^ n : ℝ) := by
    simp [uniform, PMF.uniformOfFintype_apply]
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  set r : ℝ := u / n with hrdef
  have hr : (0:ℝ) < r := by rw [hrdef]; positivity
  have hc : (0:ℝ) < Real.exp (r * u) := Real.exp_pos _
  have hbound (σ : ℝ) (s : Fin n → Fin 2) :
      Real.exp (σ * |weightDifference q s|) ≤
        Real.exp (σ * weightDifference q s) + Real.exp (-σ * weightDifference q s) := by
    by_cases hs : 0 ≤ weightDifference q s
    · rw [abs_of_nonneg hs]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos (le_of_lt (not_le.mp hs))]
      have hσ : σ * -weightDifference q s = -(σ * weightDifference q s) := by ring
      rw [hσ, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hpos (s : Fin n → Fin 2) : (0:ℝ) ≤ (uniform (Fin n → Fin 2) s).toReal :=
    ENNReal.toReal_nonneg
  -- the Markov lemma: the weighted mgf is at most exp(mu^2 n / 2)
  have hmarkov (μ : ℝ) :
      ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * Real.exp (μ * weightDifference q s) ≤
        Real.exp (μ ^ 2 * n / 2) := by
    have h2 := mgf_weighted_le q μ
    have h3 : ∀ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
        Real.exp (μ * weightDifference q s)
          = ((1:ℝ) / 2 ^ n) * Real.exp (μ * weightDifference q s) :=
      fun s => by rw [hprob s]
    rw [Finset.sum_congr rfl (fun s _ => h3 s), ← Finset.mul_sum]
    calc ((1:ℝ) / 2 ^ n) * ∑ s : Fin n → Fin 2, Real.exp (μ * weightDifference q s)
        ≤ ((1:ℝ) / 2 ^ n) * (2 ^ n * Real.exp (μ ^ 2 * n / 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (μ ^ 2 * n / 2) := by field_simp
  have hkey (μ : ℝ) :
      ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
          Real.exp (μ * |weightDifference q s|) ≤ 2 * Real.exp (μ ^ 2 * n / 2) := by
    have e1 : ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
        Real.exp (μ * weightDifference q s) ≤ Real.exp (μ ^ 2 * n / 2) := hmarkov μ
    have e2 : ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
        Real.exp (-μ * weightDifference q s) ≤ Real.exp (μ ^ 2 * n / 2) := by
      have hh := hmarkov (-μ)
      rw [neg_sq] at hh
      exact hh
    have e3 : ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
        Real.exp (μ * |weightDifference q s|)
        ≤ (∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * Real.exp (μ * weightDifference q s)) +
          (∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
            Real.exp (-μ * weightDifference q s)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro s _
      have h := mul_le_mul_of_nonneg_left (hbound μ s) (hpos s)
      rwa [mul_add] at h
    linarith
  -- Markov: X * exp(r * u) is at most 2 exp(r^2 n / 2)
  have eM : (∑ s : Fin n → Fin 2, (if u < |weightDifference q s| then (uniform (Fin n → Fin 2) s).toReal else 0)) * Real.exp (r * u)
      ≤ ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * Real.exp (r * |weightDifference q s|) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : u < |weightDifference q s|
    · simp only [hs, if_true]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_lt_mul_of_pos_left hs hr).le) (hpos s)
    · simp only [hs, if_false, zero_mul]
      exact mul_nonneg (hpos s) (Real.exp_pos (r * |weightDifference q s|)).le
  have eA : (∑ s : Fin n → Fin 2, (if u < |weightDifference q s| then (uniform (Fin n → Fin 2) s).toReal else 0)) * Real.exp (r * u)
      ≤ 2 * Real.exp (r ^ 2 * n / 2) := eM.trans (hkey r)
  -- the optimal choice r = u / n gives the exponential tail bound
  have eB : 2 * Real.exp (r ^ 2 * n / 2)
      ≤ 2 * Real.exp (-(u ^ 2) / (2 * n)) * Real.exp (r * u) := by
    have hc' : (0:ℝ) < Real.exp ((u / (n:ℝ)) * u) := Real.exp_pos _
    have hsub : Real.exp ((u / (n:ℝ)) ^ 2 * ↑n / 2) / Real.exp ((u / (n:ℝ)) * u)
        = Real.exp ((u / (n:ℝ)) ^ 2 * ↑n / 2 - (u / (n:ℝ)) * u) :=
      (Real.exp_sub _ _).symm
    rw [hrdef, ← div_le_iff₀ hc', mul_div_assoc, hsub]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hfin : (u / (n:ℝ)) ^ 2 * ↑n / 2 - (u / (n:ℝ)) * u = -(u ^ 2) / (2 * n) := by
      field_simp
      ring
    rw [hfin]

  rw [eventProb_toReal]
  exact le_of_mul_le_mul_right (eA.trans eB) hc

end
end Foundation.Quantum.QKD.Hoeffding
