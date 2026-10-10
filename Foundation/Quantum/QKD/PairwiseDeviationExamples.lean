import Foundation.Quantum.QKD.PairwiseDeviationSecurity
import Foundation.Quantum.QKD.PairwiseWeightMoments
import Foundation.Quantum.QKD.PairwiseReconciledExamples

/-! Analytical first-component checks without enumerating binary functions,
and the existing sampling derivation on a concrete coherent BB84 attack.
The full residual fixed-size sampling bound is deliberately not evaluated. -/
namespace Foundation.Quantum.QKD.PairwiseDeviationExamples
noncomputable section
open PairwiseSampling PureProjection BB84DelayedMeasurements PairwiseReconciledExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Every pair is unequal. The exact variance is 100, proved symbolically. -/
theorem unequal_variance :
    (∑ s : Fin 100 → Fin 2, (Foundation.Probability.uniform (Fin 100 → Fin 2) s).toReal *
      weightDifference (fun ib : Fin 100 × Fin 2 => ib.2) s ^ 2) = 100 := by
  simpa [mixedCount] using weightDifference_uniform_second_moment_exact (fun ib : Fin 100 × Fin 2 => ib.2)

/-- Uniformly over all fixed error patterns; no enumeration of 2^100 seeds. -/
theorem hundred_signal_tail (q : Pattern 100) :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin 100 → Fin 2))
      (fun s => (20 : ℝ) < |weightDifference q s|)).toReal ≤ 1/4 := by
  have h := weightDifference_tail q 20 (by norm_num)
  norm_num at h ⊢
  exact h

/-- Physical four-signal coherent attack, retaining its purification and the
public selector/test register in the same existing model interpretation. -/
theorem attacked_interpreted :
    let M : Finset (Fin 4) := Finset.univ
    let v := PairwiseAttackSampling.vector attack M
    let hv := PairwiseAttackSampling.unit attack M
    let hk : 1 ≤ BB84SiftedInput.selectedCount M := by norm_num [BB84SiftedInput.selectedCount, M]
    (QuantumSamplingLogic.model (distribution (BB84SiftedInput.selectedCount M) 1 hk)
      (PairwiseQuantumSampling.good 1 2) v hv (fun _ => PairwiseQuantumSampling.fallback v hv)
      (fun _ => Channel.identity _)).Carrier
        (.processed 0 (Real.sqrt (separatedBound (BB84SiftedInput.selectedCount M) 1 hk 1 1))) := by
  dsimp only
  apply PairwiseQuantumSampling.interpreted_separated
  · norm_num
  · norm_num

/-- The same analytical first-component bound reaches both final keys and
abort branches of the actual randomized protocol with the concrete attack. -/
theorem attacked_full_secure :
    IdealKey.Secure (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0)
      (1/2 + (2 * FullReconciledSecurity.separatedSamplingError 4 1 1 1 +
        FullReconciledSecurity.globalPrivacyError 4 1 1 1 2 1 0)) := by
  have h := FullReconciledSecurity.real_secure_separated (tag := 1) (length := 1)
    attack 1 2 1 0 1 1 (by norm_num) (by norm_num)
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseDeviationExamples
