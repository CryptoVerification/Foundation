import Foundation.Quantum.QKD.SiftingCountAverage

/-! A closed-form envelope for the weighted privacy error: no finite sum over
the sifted count, no maximum over counts and no enumeration of subsets,
selectors or binary patterns. The public-disclosure factor is bounded at the
largest sifted count, the error-correction factor at the shortest admissible
one, and the support radius at the largest count. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open Foundation.Quantum.QKD.PairwiseReconciledVerification
set_option backward.isDefEq.respectTransparency false

/-- Public disclosure length never decreases with the sifted count. -/
theorem publicBits_mono {a b : ℕ} (h : a ≤ b) :
    ArbitraryReconciliation.publicBits a ≤ ArbitraryReconciliation.publicBits b := by
  unfold ArbitraryReconciliation.publicBits
  omega

theorem supportRadius_mono {m n : ℕ} (k gap tolerance : ℕ) (hk : 0 < k) (h : m ≤ n) :
    PairwisePhaseCoordinates.supportRadius m k gap tolerance ≤
      PairwisePhaseCoordinates.supportRadius n k gap tolerance := by
  unfold PairwisePhaseCoordinates.supportRadius
  exact Nat.div_le_div_right (by nlinarith)

/-- A closed-form envelope for the weighted coefficient: it depends only on
the population size, the test size, the public charges and the largest
support radius. -/
def weightedCoefficientClosed (n tag k gap minKey tolerance : ℕ) (t : ℝ) : ℝ :=
  (2:ℝ) ^ ArbitraryReconciliation.publicBits (n - k) * Fintype.card (IdealKey.Key tag) *
    ((2:ℝ) ^ k *
      (((1 + t) ^ (k + minKey) / t ^ PairwisePhaseCoordinates.supportRadius n k gap tolerance) *
        (1 / 2:ℝ) ^ (k + minKey)))

/-- The closed-form envelope for the privacy-amplification error. -/
def weightedPrivacyErrorClosed (n tag length k gap minKey tolerance : ℕ) (t : ℝ) : ℝ :=
  (1 / 2:ℝ) * Real.sqrt (Fintype.card (IdealKey.Key length) *
    weightedCoefficientClosed n tag k gap minKey tolerance t)

theorem weightedCoefficientClosed_nonneg (n tag k gap minKey tolerance : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ weightedCoefficientClosed n tag k gap minKey tolerance t := by
  unfold weightedCoefficientClosed
  positivity

theorem weightedPrivacyErrorClosed_nonneg (n tag length k gap minKey tolerance : ℕ) (t : ℝ)
    (ht : 0 < t) :
    0 ≤ weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
  unfold weightedPrivacyErrorClosed
  positivity

theorem weightedCoefficient_le_closed {m n : ℕ} (tag k gap minKey tolerance : ℕ)
    (hk0 : 0 < k) (hmn : m ≤ n) (hk : k ≤ m) (hm : minKey ≤ m - k) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    weightedCoefficient m tag k gap minKey tolerance t ≤
      weightedCoefficientClosed n tag k gap minKey tolerance t := by
  have hkey : k + minKey ≤ m := by omega
  have hpow : (2:ℝ) ^ ArbitraryReconciliation.publicBits (m - k) ≤
      (2:ℝ) ^ ArbitraryReconciliation.publicBits (n - k) :=
    pow_le_pow_right₀ (by norm_num) (publicBits_mono (by omega))
  have hcard : (Fintype.card (IdealKey.Key tag) : ℝ) ≤ Fintype.card (IdealKey.Key tag) := le_rfl
  have hcard2 : (0:ℝ) ≤ Fintype.card (IdealKey.Key tag) := Nat.cast_nonneg _
  have h2k : (2:ℝ) ^ k ≤ (2:ℝ) ^ k := le_rfl
  have hrec : (1 + t) ^ m * (1 / 2:ℝ) ^ m ≤
      (1 + t) ^ (k + minKey) * (1 / 2:ℝ) ^ (k + minKey) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_of_le_one (by positivity) (by linarith) hkey
  have hrad : (1:ℝ) / t ^ PairwisePhaseCoordinates.supportRadius m k gap tolerance ≤
      1 / t ^ PairwisePhaseCoordinates.supportRadius n k gap tolerance :=
    one_div_le_one_div_of_le (pow_pos ht _)
      (pow_le_pow_of_le_one (by linarith) ht1 (supportRadius_mono k gap tolerance hk0 hmn))
  have hbracket : (1 + t) ^ m / t ^ PairwisePhaseCoordinates.supportRadius m k gap tolerance *
          (1 / 2:ℝ) ^ m ≤
        (1 + t) ^ (k + minKey) / t ^ PairwisePhaseCoordinates.supportRadius n k gap tolerance *
          (1 / 2:ℝ) ^ (k + minKey) := by
    have g1 : (1 + t) ^ m / t ^ PairwisePhaseCoordinates.supportRadius m k gap tolerance *
          (1 / 2:ℝ) ^ m = (1 + t) ^ m * (1 / 2:ℝ) ^ m *
          (1 / t ^ PairwisePhaseCoordinates.supportRadius m k gap tolerance) := by ring
    have g2 : (1 + t) ^ (k + minKey) /
            t ^ PairwisePhaseCoordinates.supportRadius n k gap tolerance * (1 / 2:ℝ) ^ (k + minKey)
          = (1 + t) ^ (k + minKey) * (1 / 2:ℝ) ^ (k + minKey) *
            (1 / t ^ PairwisePhaseCoordinates.supportRadius n k gap tolerance) := by ring
    rw [g1, g2]
    exact mul_le_mul hrec hrad (by positivity) (by positivity)
  unfold weightedCoefficient weightedCoefficientClosed
  rw [if_pos hm]
  exact mul_le_mul (mul_le_mul hpow hcard (by positivity) (by positivity))
    (mul_le_mul h2k hbracket (by positivity) (by positivity)) (by positivity) (by positivity)

theorem weightedPrivacyError_le_closed {m n : ℕ} (tag length k gap minKey tolerance : ℕ)
    (hk0 : 0 < k) (hmn : m ≤ n) (hk : k ≤ m) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    weightedPrivacyError m tag length k gap minKey tolerance t ≤
      weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
  by_cases hm : minKey ≤ m - k
  · unfold weightedPrivacyErrorClosed weightedPrivacyError
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left
      (weightedCoefficient_le_closed tag k gap minKey tolerance hk0 hmn hk hm t ht ht1)
      (Nat.cast_nonneg _)
  · unfold weightedPrivacyError weightedCoefficient
    rw [if_neg hm]
    simp only [mul_zero, Real.sqrt_zero, mul_zero]
    exact weightedPrivacyErrorClosed_nonneg n tag length k gap minKey tolerance t ht

/-- The sifting-set average is bounded by the closed-form envelope: the
binomial weights sum to one, so the average is at most the envelope. -/
theorem countWeightedError_le_closed (n tag length k gap minKey tolerance : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hk0 : 0 < k) :
    countWeightedError n tag length k gap minKey tolerance t ≤
      weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
  have hbound (m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
      ((Nat.choose n m : ℝ) / (2:ℝ) ^ n) *
        (if k ≤ m then weightedPrivacyError m tag length k gap minKey tolerance t else 0) ≤
        ((Nat.choose n m : ℝ) / (2:ℝ) ^ n) *
          weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split_ifs with hk
    · exact weightedPrivacyError_le_closed tag length k gap minKey tolerance hk0
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hk t ht ht1
    · exact weightedPrivacyErrorClosed_nonneg n tag length k gap minKey tolerance t ht
  unfold countWeightedError
  calc ∑ m ∈ Finset.range (n + 1),
        ((Nat.choose n m : ℝ) / (2:ℝ) ^ n) *
          (if k ≤ m then weightedPrivacyError m tag length k gap minKey tolerance t else 0)
      ≤ ∑ m ∈ Finset.range (n + 1),
          ((Nat.choose n m : ℝ) / (2:ℝ) ^ n) *
            weightedPrivacyErrorClosed n tag length k gap minKey tolerance t :=
        Finset.sum_le_sum hbound
    _ = ((∑ m ∈ Finset.range (n + 1), (Nat.choose n m : ℝ)) / (2:ℝ) ^ n) *
          weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
        rw [← Finset.sum_mul, Finset.sum_div]
    _ = weightedPrivacyErrorClosed n tag length k gap minKey tolerance t := by
        have hc : (∑ m ∈ Finset.range (n + 1), (Nat.choose n m : ℝ)) = (2:ℝ) ^ n := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          simp
        rw [hc, div_self (by positivity), one_mul]

/-- A purely numerical criterion for the closed-form envelope. -/
theorem weightedPrivacyErrorClosed_le (n tag length k gap minKey tolerance : ℕ)
    (t ε : ℝ) (hε : 0 ≤ ε)
    (h : Fintype.card (IdealKey.Key length) *
        weightedCoefficientClosed n tag k gap minKey tolerance t ≤ (2 * ε) ^ 2) :
    weightedPrivacyErrorClosed n tag length k gap minKey tolerance t ≤ ε := by
  have hs := Real.sqrt_le_iff.mpr ⟨by positivity, h⟩
  unfold weightedPrivacyErrorClosed
  linarith

end
end Foundation.Quantum.QKD.FullReconciledSecurity

/-! The total error of the full BB84 output with every term closed: the
collision term, the sampling term and the privacy term are closed
expressions, and no finite sum over sifted counts, subsets or selectors
remains. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open Foundation.Quantum.QKD.PairwiseReconciledVerification
set_option backward.isDefEq.respectTransparency false

theorem real_secure_closed {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (hg : 0 < gap)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2 * Real.sqrt (PairwiseSampling.gapBound n k gap) +
          weightedPrivacyErrorClosed n tag length k gap minKey tolerance t)) := by
  have h := real_secure_count (tag := tag) (length := length) A k gap minKey tolerance hk0 hg t ht ht1
  have he := countWeightedError_le_closed n tag length k gap minKey tolerance t ht ht1 hk0
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
