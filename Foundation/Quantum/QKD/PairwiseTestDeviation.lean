import Foundation.Quantum.QKD.SamplingVariance
import Foundation.Quantum.QKD.PairwiseDeviationSecurity

/-! The actual without-replacement test component has a uniform analytical
bound. It removes the residual finite maximum from the separated sampling
bound, for arbitrary fixed error patterns and every sample size. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def selectedErrors {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => q (i,s i) = 1)

theorem selectedErrors_card {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) :
    (selectedErrors q s).card = selectedWeight q s := rfl

theorem hits_tested {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) (T : Finset (Fin n)) :
    Sampling.hits (selectedErrors q s) T = (tested q (s,T) : ℝ) := by
  rw [Sampling.hits_card]
  unfold selectedErrors tested
  apply congrArg (fun S : Finset (Fin n) => (S.card : ℝ))
  ext i
  simp [and_comm]

theorem sampleDifference_centered {n : Nat} (k : Nat) (q : Pattern n)
    (s : Fin n → Fin 2) (T : Finset (Fin n)) :
    sampleDifference k q (s,T) = Sampling.centered k (selectedErrors q s) T := by
  rw [Sampling.centered, hits_tested, selectedErrors_card]
  rfl

theorem conditional_sample_tail {n : Nat} (k : Nat) (hk : k ≤ n) (q : Pattern n)
    (s : Fin n → Fin 2) (u : ℝ) (hu : 0 < u) :
    (eventProb (Sampling.fullSample n k hk) (fun T => u < |sampleDifference k q (s,T)|)).toReal ≤
      (k : ℝ)*n^2/(4*u^2) := by
  simpa only [sampleDifference_centered] using Sampling.centered_tail_all k hk (selectedErrors q s) u hu

theorem sampleDifference_tail {n : Nat} (k : Nat) (hk : k ≤ n) (q : Pattern n)
    (u : ℝ) (hu : 0 < u) :
    (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal ≤
      (k : ℝ)*n^2/(4*u^2) := by
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
    _ ≤ ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * ((k : ℝ)*n^2/(4*u^2)) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (conditional_sample_tail k hk q s u hu) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

def polynomialBound (n k : Nat) (u t : ℝ) : ℝ := n/t^2 + (k : ℝ)*n^2/(4*u^2)

theorem sampleTailBound_polynomial (n k : Nat) (hk : k ≤ n) (u : ℝ) (hu : 0 < u) :
    sampleTailBound n k hk u ≤ (k : ℝ)*n^2/(4*u^2) := by
  unfold sampleTailBound
  apply Finset.sup'_le
  intro q _
  exact sampleDifference_tail k hk q u hu

theorem separatedBound_polynomial (n k : Nat) (hk : k ≤ n) (u t : ℝ) (hu : 0 < u) :
    separatedBound n k hk u t ≤ polynomialBound n k u t := by
  unfold separatedBound polynomialBound
  linarith [sampleTailBound_polynomial n k hk u hu]

/-- Both components are now analytical. No maximum over binary patterns or
selectors occurs on the right-hand side. -/
theorem classical_polynomial (n k gap : Nat) (hk : k ≤ n) (q : Pattern n) (u t : ℝ)
    (hu : 0 < u) (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    (eventProb (distribution n k hk) (bad k gap q)).toReal ≤ polynomialBound n k u t :=
  (classical_separated n k gap hk u t ht hgap q).trans (separatedBound_polynomial n k hk u t hu)

theorem errorBound_polynomial (n k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (hu : 0 < u) (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    (errorBound n k gap).toReal ≤ polynomialBound n k u t :=
  (errorBound_separated n k gap hk u t ht hgap).trans (separatedBound_polynomial n k hk u t hu)

end
end Foundation.Quantum.QKD.PairwiseSampling
