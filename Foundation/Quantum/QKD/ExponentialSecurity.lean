import Foundation.Quantum.QKD.SamplingExponential
import Foundation.Quantum.QKD.PairwiseTestDeviation
import Foundation.Quantum.QKD.WeightedClosed

/-! Exponential sampling error for the actual normalized BB84 output.
The public classical channel is authentic by the existing protocol model. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

theorem sampleDifference_tail_exp {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (hk0 : 0 < k) (q : Pattern n) (u : ℝ) (hu : 0 < u) :
    (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal ≤
      2 * Real.exp (-2 * u ^ 2 / ((n : ℝ) ^ 2 * k)) := by
  rw [independent, eventProb_bind_toReal]
  have he (s : Fin n → Fin 2) :
      eventProb ((Sampling.sample (Finset.univ : Finset (Fin n)) k (by simpa using hk)).map (fun T => (s,T)))
        (fun c => u < |sampleDifference k q c|) =
      eventProb (Sampling.fullSample n k hk) (fun T => u < |sampleDifference k q (s,T)|) := by
    unfold eventProb
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  simp_rw [he]
  calc
    _ ≤ ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal *
        (2 * Real.exp (-2 * u ^ 2 / ((n : ℝ) ^ 2 * k))) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa only [sampleDifference_centered] using
        Sampling.centered_tail_exp hn k hk hk0 (selectedErrors q s) u hu
    _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

/-- Closed exponential envelope after splitting the gap equally between
the selector and the fixed-size test deviations. -/
def exponentialGapBound (n k gap : ℕ) : ℝ :=
  2 * Real.exp (-(gap : ℝ) ^ 2 / (8 * (k : ℝ) ^ 2 * n)) +
  2 * Real.exp (-(gap : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2 * k))

theorem classical_exponential (n k gap : ℕ) (hk : k ≤ n) (hk0 : 0 < k)
    (hg : 0 < gap) (q : Pattern n) :
    (eventProb (distribution n k hk) (bad k gap q)).toReal ≤ exponentialGapBound n k gap := by
  have hn : 0 < n := by omega
  have h := classical_decomposition_bound_exp k gap hk q ((gap : ℝ) / 2)
    ((gap : ℝ) / (2 * k)) (by positivity) hn (by
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp
      linarith)
  have hs := sampleDifference_tail_exp hn k hk hk0 q ((gap : ℝ) / 2) (by positivity)
  have he1 : -(((gap : ℝ) / (2 * k)) ^ 2) / (2 * n) =
      -(gap : ℝ) ^ 2 / (8 * (k : ℝ) ^ 2 * n) := by ring
  have he2 : -2 * ((gap : ℝ) / 2) ^ 2 / ((n : ℝ) ^ 2 * k) =
      -(gap : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2 * k) := by ring
  rw [he1] at h
  rw [he2] at hs
  unfold exponentialGapBound
  linarith

theorem errorBound_exponential (n k gap : ℕ) (hk : k ≤ n) (hk0 : 0 < k) (hg : 0 < gap) :
    (errorBound n k gap).toReal ≤ exponentialGapBound n k gap := by
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Pattern n))
    Finset.univ_nonempty (badCount n k gap)
  have he : eventProb (distribution n k hk) (bad k gap q) = errorBound n k gap := by
    rw [probability_count]
    unfold errorBound maxBadCount
    rw [hq]
  have h := classical_exponential n k gap hk hk0 hg q
  rwa [he] at h

theorem exponentialGapBound_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (k gap : ℕ) (hk0 : 0 < k) :
    exponentialGapBound m k gap ≤ exponentialGapBound n k gap := by
  unfold exponentialGapBound
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left hmnR (by positivity))
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((n : ℝ) - m)]) (by positivity))

end
end Foundation.Quantum.QKD.PairwiseSampling

namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

theorem sampling_error_exponential (n k gap : ℕ) (hk0 : 0 < k) (hg : 0 < gap) :
    PairwiseRandomizedSampling.error n k gap ≤
      Real.sqrt (PairwiseSampling.exponentialGapBound n k gap) := by
  unfold PairwiseRandomizedSampling.error
  calc
    _ ≤ ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
        Real.sqrt (PairwiseSampling.exponentialGapBound n k gap) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      unfold PairwiseRandomizedSampling.conditionalError
      split_ifs with hk
      · have hm : selectedCount M ≤ n := by
          simpa only [selectedCount, Fintype.card_coe] using
            (show M.card ≤ n by simpa using Finset.card_le_univ M)
        exact Real.sqrt_le_sqrt ((PairwiseSampling.errorBound_exponential (selectedCount M) k gap hk hk0 hg).trans
          (PairwiseSampling.exponentialGapBound_mono (by omega) hm k gap hk0))
      · exact Real.sqrt_nonneg _
    _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

/-- The full two-key real/ideal comparison, with an exponential sampling
bound and the one-dimensional privacy-amplification average. -/
theorem real_secure_exponential {n tag length : ℕ} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : ℕ) (hk0 : 0 < k) (hg : 0 < gap)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2 * Real.sqrt (PairwiseSampling.exponentialGapBound n k gap) +
          countWeightedError n tag length k gap minKey tolerance t)) := by
  have h := real_verified_secure (tag := tag) (length := length) A k gap minKey tolerance
  have hs := sampling_error_exponential n k gap hk0 hg
  have hp := global_privacy_le_weighted n tag length k gap minKey tolerance hk0 t ht ht1
  rw [globalWeightedError_count] at hp
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
