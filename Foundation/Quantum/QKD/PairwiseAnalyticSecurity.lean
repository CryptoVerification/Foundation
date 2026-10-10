import Foundation.Quantum.QKD.PairwiseTestDeviation

/-! A closed polynomial sampling bound and its interpretation in the same
coherent quantum experiment and full reconciled BB84 protocol. No residual
maximum or sum over classical patterns occurs in this sampling error. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gapBound (n k gap : Nat) : ℝ := (n : ℝ)*k*(n+4*k)/(gap : ℝ)^2

theorem polynomial_gap (n k gap : Nat) (hk : 0 < k) (hg : 0 < gap) :
    polynomialBound n k ((gap : ℝ)/2) ((gap : ℝ)/(2*k)) = gapBound n k gap := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hg0 : (gap : ℝ) ≠ 0 := by positivity
  unfold polynomialBound gapBound
  field_simp
  ring

theorem errorBound_gap (n k gap : Nat) (hk : k ≤ n) (hk0 : 0 < k) (hg : 0 < gap) :
    (errorBound n k gap).toReal ≤ gapBound n k gap := by
  have hsum : (gap : ℝ)/2 + k*((gap : ℝ)/(2*k)) ≤ gap := by
    have hk' : (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring_nf
    norm_num
  have h := errorBound_polynomial n k gap hk ((gap : ℝ)/2) ((gap : ℝ)/(2*k))
    (by positivity) (by positivity) hsum
  simpa only [polynomial_gap n k gap hk0 hg] using h

theorem gapBound_mono {m n : Nat} (hmn : m ≤ n) (k gap : Nat) :
    gapBound m k gap ≤ gapBound n k gap := by
  unfold gapBound
  have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
  gcongr

end
end Foundation.Quantum.QKD.PairwiseSampling

namespace Foundation.Quantum.QKD.PairwiseQuantumSampling
noncomputable section
open PureProjection BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

theorem approximation_gap {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) (hk0 : 0 < k) (hg : 0 < gap) :
    OperatorApprox (QuantumSampling.real (PairwiseSampling.distribution n k hk) v)
      (QuantumSampling.ideal (PairwiseSampling.distribution n k hk) (good k gap) v
        (fun _ => fallback v hv)) (Real.sqrt (PairwiseSampling.gapBound n k gap)) :=
  (approximation v hv k gap hk).weaken (Real.sqrt_le_sqrt (PairwiseSampling.errorBound_gap n k gap hk hk0 hg))

theorem interpreted_gap {n : Nat} {e b : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) (hk0 : 0 < k) (hg : 0 < gap)
    (C : Nat → Channel (Guessing.publicSpace (PairwiseSampling.Configuration n) (jointSpace n e)) b) :
    (QuantumSamplingLogic.model (PairwiseSampling.distribution n k hk) (good k gap) v hv
      (fun _ => fallback v hv) C).Carrier (.processed 0 (Real.sqrt (PairwiseSampling.gapBound n k gap))) := by
  apply QuantumSamplingLogic.sound _ _ v hv _ C
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.gapBound n k gap))
  intro _
  exact fun i => (classical k gap hk i).trans (PairwiseSampling.errorBound_gap n k gap hk hk0 hg)

end
end Foundation.Quantum.QKD.PairwiseQuantumSampling

namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

theorem sampling_error_gap (n k gap : Nat) (hk0 : 0 < k) (hg : 0 < gap) :
    PairwiseRandomizedSampling.error n k gap ≤ Real.sqrt (PairwiseSampling.gapBound n k gap) := by
  unfold PairwiseRandomizedSampling.error
  calc
    _ ≤ ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
        Real.sqrt (PairwiseSampling.gapBound n k gap) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      unfold PairwiseRandomizedSampling.conditionalError
      split_ifs with hk
      · have hm : selectedCount M ≤ n := by
          simpa only [selectedCount, Fintype.card_coe] using
            (show M.card ≤ n by simpa using Finset.card_le_univ M)
        exact Real.sqrt_le_sqrt ((PairwiseSampling.errorBound_gap (selectedCount M) k gap hk hk0 hg).trans
          (PairwiseSampling.gapBound_mono hm k gap))
      · exact Real.sqrt_nonneg _
    _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

/-- Sampling error now has a closed bound independent of finite enumeration;
the privacy term still includes the exact support counts and public leakage. -/
theorem real_secure_gap {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (hk0 : 0 < k) (hg : 0 < gap) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*Real.sqrt (PairwiseSampling.gapBound n k gap) + globalPrivacyError n tag length k gap minKey tolerance)) := by
  have h := real_verified_secure (tag := tag) (length := length) A k gap minKey tolerance
  have he := sampling_error_gap n k gap hk0 hg
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
