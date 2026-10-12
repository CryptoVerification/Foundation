import Foundation.Quantum.QKD.SamplingBernoulli
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Exponential moments of a uniform sample without replacement.
All populations are fixed; no independence of population errors is assumed. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- The falling-factorial inclusion ratio is bounded by the corresponding
independent inclusion power. -/
theorem choose_ratio_le {n w : ℕ} (hn : 0 < n) (hw : w ≤ n) (r : ℕ) :
    (Nat.choose w r : ℝ) ≤ ((w : ℝ) / n) ^ r * (Nat.choose n r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hr : r < w
    · have hrw : r ≤ w := by omega
      have hrn : r ≤ n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hwR : (w : ℝ) ≤ n := by exact_mod_cast hw
      have ha : (0 : ℝ) ≤ (w : ℝ) - r := by
        have h : (r : ℝ) ≤ w := by exact_mod_cast hrw
        linarith
      have hstep : (w : ℝ) - r ≤ (w : ℝ) / n * ((n : ℝ) - r) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hnR).mpr
        nlinarith [mul_le_mul_of_nonneg_left hwR (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
      have ew : (Nat.choose w (r + 1) : ℝ) * (r + 1) =
          (Nat.choose w r : ℝ) * ((w : ℝ) - r) := by
        have h := Nat.choose_succ_right_eq w r
        exact_mod_cast h
      have en : (Nat.choose n (r + 1) : ℝ) * (r + 1) =
          (Nat.choose n r : ℝ) * ((n : ℝ) - r) := by
        have h := Nat.choose_succ_right_eq n r
        exact_mod_cast h
      have hmul : (Nat.choose w (r + 1) : ℝ) * (r + 1) ≤
          (((w : ℝ) / n) ^ (r + 1) * (Nat.choose n (r + 1) : ℝ)) * (r + 1) := by
        calc
          _ = (Nat.choose w r : ℝ) * ((w : ℝ) - r) := ew
          _ ≤ (((w : ℝ) / n) ^ r * (Nat.choose n r : ℝ)) * ((w : ℝ) - r) :=
            mul_le_mul_of_nonneg_right ih ha
          _ ≤ (((w : ℝ) / n) ^ r * (Nat.choose n r : ℝ)) *
              ((w : ℝ) / n * ((n : ℝ) - r)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = ((w : ℝ) / n) ^ (r + 1) *
              ((Nat.choose n r : ℝ) * ((n : ℝ) - r)) := by rw [pow_succ]; ring
          _ = _ := by rw [← en]; ring
      exact (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < r + 1)).mp hmul
    · have hz : Nat.choose w (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, Nat.cast_zero]
      positivity

/-- Exact joint inclusion probability, in symmetric binomial-ratio form. -/
theorem fullSample_subset_real {n : ℕ} (k : ℕ) (hk : k ≤ n) (E : Finset (Fin n)) :
    (eventProb (fullSample n k hk) (fun T => E ⊆ T)).toReal =
      (Nat.choose k E.card : ℝ) / (Nat.choose n E.card : ℝ) := by
  have hEn : E.card ≤ n := by simpa using Finset.card_le_univ E
  have hc : (Nat.choose n E.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hEn).ne'
  have hkC : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  by_cases hEk : E.card ≤ k
  · rw [fullSample, subset_probability Finset.univ E k (by simpa using hk)
        (Finset.subset_univ E) hEk]
    simp only [Finset.card_univ, Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast]
    have hid : (Nat.choose n k : ℝ) * (Nat.choose k E.card : ℝ) =
        (Nat.choose n E.card : ℝ) * (Nat.choose (n - E.card) (k - E.card) : ℝ) := by
      exact_mod_cast (Nat.choose_mul (n := n) hEk)
    field_simp
    nlinarith [hid]
  · rw [fullSample, subset_too_large Finset.univ E k (by simpa using hk) (by omega)]
    rw [Nat.choose_eq_zero_of_lt (by omega : k < E.card)]
    simp

/-- Partition a powerset sum by subset cardinality. -/
theorem powerset_sum_card {n : ℕ} (U : Finset (Fin n)) (f : ℕ → ℝ) :
    (∑ F ∈ U.powerset, f F.card) =
      ∑ r ∈ Finset.range (n + 1), (Nat.choose U.card r : ℝ) * f r := by
  classical
  have hf : U.powerset.filter (fun F => F.card ∈ Finset.range (n + 1)) = U.powerset := by
    apply Finset.filter_eq_self.mpr
    intro F hF
    have h : F.card ≤ n := by simpa using Finset.card_le_univ F
    simp only [Finset.mem_range]
    omega
  have h := Finset.sum_fiberwise_eq_sum_filter U.powerset (Finset.range (n + 1))
    Finset.card (fun F => f F.card)
  rw [hf] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  have he : U.powerset.filter (fun F => F.card = r) = U.powersetCard r := by
    ext F
    simp [Finset.mem_powersetCard, Finset.mem_powerset]
  rw [he]
  calc
    (∑ F ∈ U.powersetCard r, f F.card) = ∑ _F ∈ U.powersetCard r, f r := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_powersetCard.mp hF).2]
    _ = _ := by simp [Finset.card_powersetCard]

/-- Exact exponential-moment expansion in joint inclusion events. -/
theorem fullSample_mgf_expansion {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (E : Finset (Fin n)) (θ : ℝ) :
    expectation (fullSample n k hk) (fun T => Real.exp (θ * hits E T)) =
      ∑ F ∈ E.powerset, (Real.exp θ - 1) ^ F.card *
        (eventProb (fullSample n k hk) (fun T => F ⊆ T)).toReal := by
  classical
  have hpoint (T : Finset (Fin n)) : Real.exp (θ * hits E T) =
      ∑ F ∈ E.powerset, (Real.exp θ - 1) ^ F.card * (if F ⊆ T then 1 else 0) := by
    have hi (i : Fin n) : Real.exp (θ * indicator T i) =
        (Real.exp θ - 1) * indicator T i + 1 := by
      unfold indicator
      by_cases h : i ∈ T <;> simp [h]
    unfold hits
    rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [hi]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro F _
    simp only [Finset.prod_mul_distrib, Finset.prod_const,
      indicator, Finset.prod_boole]
    simp [Finset.subset_iff]
  simp_rw [hpoint]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [eventProb_toReal]
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : F ⊆ T
  · simp only [if_pos h]
    ring
  · simp [h]

/-- Sampling without replacement has no larger upper exponential moment
than `k` independent Bernoulli trials of mean `E.card / n`. -/
theorem fullSample_mgf_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (E : Finset (Fin n)) (θ : ℝ) (hθ : 0 ≤ θ) :
    expectation (fullSample n k hk) (fun T => Real.exp (θ * hits E T)) ≤
      (1 + ((E.card : ℝ) / n) * (Real.exp θ - 1)) ^ k := by
  classical
  have hEn : E.card ≤ n := by simpa using Finset.card_le_univ E
  have ha : 0 ≤ Real.exp θ - 1 := by
    have h : 1 ≤ Real.exp θ := by simpa using Real.exp_le_exp.mpr hθ
    linarith
  rw [fullSample_mgf_expansion]
  simp_rw [fullSample_subset_real]
  rw [powerset_sum_card E (fun r => (Real.exp θ - 1) ^ r *
    ((Nat.choose k r : ℝ) / (Nat.choose n r : ℝ)))]
  calc
    _ ≤ ∑ r ∈ Finset.range (n + 1), (Nat.choose k r : ℝ) *
        (((E.card : ℝ) / n) * (Real.exp θ - 1)) ^ r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrn : r ≤ n := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hc : 0 < (Nat.choose n r : ℝ) := by exact_mod_cast Nat.choose_pos hrn
      have hb := choose_ratio_le hn hEn r
      have hd : (Nat.choose E.card r : ℝ) / (Nat.choose n r : ℝ) ≤
          ((E.card : ℝ) / n) ^ r := (div_le_iff₀ hc).mpr hb
      have hm := mul_le_mul_of_nonneg_left hd
        (show 0 ≤ (Nat.choose k r : ℝ) * (Real.exp θ - 1) ^ r by positivity)
      rw [mul_pow]
      convert hm using 1 <;> ring
    _ = (1 + ((E.card : ℝ) / n) * (Real.exp θ - 1)) ^ k := by
      have hz (r : ℕ) (hr : r ∈ Finset.range (n + 1)) (hrk : r ∉ Finset.range (k + 1)) :
          (Nat.choose k r : ℝ) * (((E.card : ℝ) / n) * (Real.exp θ - 1)) ^ r = 0 := by
        have hkr : k < r := by simp only [Finset.mem_range] at hrk; omega
        rw [Nat.choose_eq_zero_of_lt hkr]
        simp
      rw [← Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ n + 1)) hz]
      simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
        (add_pow (((E.card : ℝ) / n) * (Real.exp θ - 1)) 1 k).symm

/-- Sub-Gaussian exponential moment for the integer-scaled deviation. -/
theorem centered_mgf_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (E : Finset (Fin n)) (θ : ℝ) (hθ : 0 ≤ θ) :
    expectation (fullSample n k hk) (fun T => Real.exp (θ * centered k E T)) ≤
      Real.exp (θ ^ 2 * (n : ℝ) ^ 2 * k / 8) := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hEn : (E.card : ℝ) ≤ n := by exact_mod_cast (show E.card ≤ n by simpa using Finset.card_le_univ E)
  let p : ℝ := (E.card : ℝ) / n
  let s : ℝ := θ * n
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; exact (div_le_one (by positivity)).mpr hEn
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have he (T : Finset (Fin n)) : Real.exp (θ * centered k E T) =
      Real.exp (s * hits E T) * Real.exp (-θ * k * E.card) := by
    rw [← Real.exp_add]
    congr 1
    unfold centered s
    ring
  simp_rw [he]
  rw [expectation_mul_const]
  have hsingle : Real.exp (-p * s) * (1 - p + p * Real.exp s) ≤ Real.exp (s ^ 2 / 8) := by
    have h := Bernoulli.hoeffding_lemma p s hp0 hp1
    have heq : Real.exp (-p * s) * (1 - p + p * Real.exp s) =
        (1 - p) * Real.exp (-(p * s)) + p * Real.exp ((1 - p) * s) := by
      have hx : Real.exp (-p * s) * Real.exp s = Real.exp ((1 - p) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [mul_add]
      calc
        _ = (1 - p) * Real.exp (-(p * s)) + p * (Real.exp (-p * s) * Real.exp s) := by
          rw [neg_mul]; ring
        _ = _ := by rw [hx]
    rwa [← heq] at h
  calc
    _ ≤ (1 + p * (Real.exp s - 1)) ^ k * Real.exp (-θ * k * E.card) :=
      mul_le_mul_of_nonneg_right (fullSample_mgf_le hn k hk E s hs) (Real.exp_nonneg _)
    _ = (Real.exp (-p * s) * (1 - p + p * Real.exp s)) ^ k := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hbase : 1 + p * (Real.exp s - 1) = 1 - p + p * Real.exp s := by ring
      rw [hbase]
      have harg : (k : ℝ) * (-p * s) = -θ * k * E.card := by
        dsimp [p, s]
        field_simp
      rw [harg]
      ring
    _ ≤ (Real.exp (s ^ 2 / 8)) ^ k :=
      pow_le_pow_left₀ (by positivity) hsingle k
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [s]
      ring

/-- Finite exponential Markov bound; no measure-theoretic conditioning is
needed in the PMF model. -/
theorem exponential_markov {X : Type} [Fintype X] (p : PMF X) (f : X → ℝ)
    (θ u : ℝ) (hθ : 0 ≤ θ) :
    (eventProb p (fun x => u < f x)).toReal ≤
      Real.exp (-θ * u) * expectation p (fun x => Real.exp (θ * f x)) := by
  classical
  rw [eventProb_toReal]
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : u < f x
  · rw [if_pos hx]
    have harg : 0 ≤ -θ * u + θ * f x := by nlinarith
    have he : 1 ≤ Real.exp (-θ * u + θ * f x) := by
      simpa using Real.exp_le_exp.mpr harg
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg)
    rw [Real.exp_add] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · rw [if_neg hx]
    positivity

/-- One-sided Hoeffding bound for the actual fixed-size subset distribution. -/
theorem centered_upper_tail_exp {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (hk0 : 0 < k) (E : Finset (Fin n)) (u : ℝ) (hu : 0 < u) :
    (eventProb (fullSample n k hk) (fun T => u < centered k E T)).toReal ≤
      Real.exp (-2 * u ^ 2 / ((n : ℝ) ^ 2 * k)) := by
  let θ : ℝ := 4 * u / ((n : ℝ) ^ 2 * k)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  calc
    _ ≤ Real.exp (-θ * u) * expectation (fullSample n k hk)
        (fun T => Real.exp (θ * centered k E T)) :=
      exponential_markov _ _ θ u hθ
    _ ≤ Real.exp (-θ * u) * Real.exp (θ ^ 2 * (n : ℝ) ^ 2 * k / 8) :=
      mul_le_mul_of_nonneg_left (centered_mgf_le hn k hk E θ hθ) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [θ]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- Complementing the population errors negates the deviation on every
sample in the support of `fullSample`. -/
theorem centered_compl {n : ℕ} (k : ℕ) (E T : Finset (Fin n)) (hT : T.card = k) :
    centered k Eᶜ T = -centered k E T := by
  classical
  have hhit : hits Eᶜ T = (k : ℝ) - hits E T := by
    rw [hits_card, hits_card]
    have hc : (Eᶜ ∩ T).card + (E ∩ T).card = T.card := by
      have h := Finset.card_sdiff_add_card_inter T E
      simpa [Finset.inter_comm, Finset.sdiff_eq_inter_compl] using h
    have hr : ((Eᶜ ∩ T).card : ℝ) + (E ∩ T).card = k := by exact_mod_cast hc.trans hT
    linarith
  have hEc : (Eᶜ.card : ℝ) = (n : ℝ) - E.card := by
    rw [Finset.card_compl]
    have hEn : E.card ≤ n := by simpa using Finset.card_le_univ E
    simp [Nat.cast_sub hEn]
  unfold centered
  rw [hhit, hEc]
  ring

/-- Two-sided sampling-without-replacement exponential bound, uniform over
all fixed error sets. -/
theorem centered_tail_exp {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (hk0 : 0 < k) (E : Finset (Fin n)) (u : ℝ) (hu : 0 < u) :
    (eventProb (fullSample n k hk) (fun T => u < |centered k E T|)).toReal ≤
      2 * Real.exp (-2 * u ^ 2 / ((n : ℝ) ^ 2 * k)) := by
  classical
  have hunion : (eventProb (fullSample n k hk) (fun T => u < |centered k E T|)).toReal ≤
      (eventProb (fullSample n k hk) (fun T => u < centered k E T)).toReal +
      (eventProb (fullSample n k hk) (fun T => u < centered k Eᶜ T)).toReal := by
    rw [eventProb_toReal, eventProb_toReal, eventProb_toReal, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro T _
    by_cases hT : T.card = k
    · rw [centered_compl k E T hT]
      by_cases he : u < |centered k E T|
      · rw [if_pos he]
        have hp := lt_abs.mp he
        rcases hp with hp | hp <;> simp only [if_pos hp] <;>
          split_ifs <;> linarith [show 0 ≤ (fullSample n k hk T).toReal from ENNReal.toReal_nonneg]
      · rw [if_neg he]
        positivity
    · simp [fullSample_of_card_ne k hk T hT]
  have ha := centered_upper_tail_exp hn k hk hk0 E u hu
  have hb := centered_upper_tail_exp hn k hk hk0 Eᶜ u hu
  linarith

end
end Foundation.Quantum.QKD.Sampling
