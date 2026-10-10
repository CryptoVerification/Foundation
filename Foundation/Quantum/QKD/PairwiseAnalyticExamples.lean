import Foundation.Quantum.QKD.PairwiseAnalyticSecurity
import Foundation.Quantum.QKD.PairwiseReconciledExamples

/-! Exact dependent sampling checks, analytical large-population bounds
without enumerating subsets or selectors, and a concrete coherent BB84
interpretation. These sampling estimates alone are not useful-key claims. -/
namespace Foundation.Quantum.QKD.PairwiseAnalyticExamples
noncomputable section
open Sampling PairwiseSampling PairwiseReconciledExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem single_inclusion :
    (Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T)).toReal = 1/5 := by
  have h : (Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T)).toReal = (20 : ℝ)/(Finset.univ : Finset (Fin 100)).card :=
    singleton_probability_real Finset.univ 20 (by decide) 0 (Finset.mem_univ _)
  norm_num at h ⊢
  exact h

/-- 19/495 is strictly below the independent product (1/5)^2. -/
theorem pair_inclusion :
    (Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T ∧ (1 : Fin 100) ∈ T)).toReal = 19/495 := by
  have h : (Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T ∧ (1 : Fin 100) ∈ T)).toReal =
      (20 : ℝ)*(20-1)/(((Finset.univ : Finset (Fin 100)).card : ℝ)*((Finset.univ : Finset (Fin 100)).card-1)) :=
    pair_probability_real Finset.univ 20 (by decide) 0 1 (Finset.mem_univ _) (Finset.mem_univ _) (by decide)
  norm_num at h ⊢
  exact h

theorem pair_negative_dependence :
    (Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T ∧ (1 : Fin 100) ∈ T)).toReal <
    ((Foundation.Probability.eventProb (fullSample 100 20 (by decide))
      (fun T => (0 : Fin 100) ∈ T)).toReal)^2 := by
  rw [pair_inclusion, single_inclusion]
  norm_num

theorem two_error_variance :
    expectation (fullSample 100 20 (by decide)) (fun T => centered 20 ({0,1} : Finset (Fin 100)) T ^ 2) =
      313600/99 := by
  have h := centered_second_moment (n := 100) (by decide) 20 (by decide) ({0,1} : Finset (Fin 100))
  norm_num at h ⊢
  exact h

/-- All fixed error sets in 1000 positions; the test has exactly 100 positions. -/
theorem thousand_test_tail (E : Finset (Fin 1000)) :
    (Foundation.Probability.eventProb (fullSample 1000 100 (by decide))
      (fun T => (20000 : ℝ) < |centered 100 E T|)).toReal ≤ 1/16 := by
  have h := centered_tail_all 100 (show 100 ≤ 1000 by decide) E 20000 (by norm_num)
  norm_num at h ⊢
  exact h

/-- Exact worst-case classical sampling error, bounded without enumerating
4^1000000 patterns, 2^1000000 selectors or fixed-size subsets. -/
theorem million_sampling_bound :
    (errorBound 1000000 100000 10000000000).toReal ≤ 7/5000 := by
  have h := errorBound_gap 1000000 100000 10000000000 (by decide) (by decide) (by decide)
  norm_num [gapBound] at h ⊢
  exact h

theorem attacked_interpreted :
    let M : Finset (Fin 4) := Finset.univ
    let v := PairwiseAttackSampling.vector attack M
    let hv := PairwiseAttackSampling.unit attack M
    let hk : 1 ≤ BB84SiftedInput.selectedCount M := by norm_num [BB84SiftedInput.selectedCount,M]
    (QuantumSamplingLogic.model (distribution (BB84SiftedInput.selectedCount M) 1 hk)
      (PairwiseQuantumSampling.good 1 2) v hv (fun _ => PairwiseQuantumSampling.fallback v hv)
      (fun _ => Channel.identity _)).Carrier
        (.processed 0 (Real.sqrt (gapBound (BB84SiftedInput.selectedCount M) 1 2))) := by
  dsimp only
  apply PairwiseQuantumSampling.interpreted_gap
  · decide
  · decide

/-- Both real final keys, original public information, Eve and every abort. -/
theorem attacked_full_secure :
    IdealKey.Secure (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0)
      (1/2 + (2 * Real.sqrt (gapBound 4 1 2) + FullReconciledSecurity.globalPrivacyError 4 1 1 1 2 1 0)) := by
  have h := FullReconciledSecurity.real_secure_gap (tag := 1) (length := 1) attack 1 2 1 0 (by decide) (by decide)
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseAnalyticExamples
