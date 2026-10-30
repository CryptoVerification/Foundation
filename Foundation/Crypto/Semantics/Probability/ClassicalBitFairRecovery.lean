import Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicSampler
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryError
import Foundation.Crypto.Semantics.Probability.FiniteFairSampling
import Foundation.Crypto.Semantics.Probability.FiniteKernelVariation

/-! A different pair of conditional kernels on the full-support five-state
edge. Every row uses twelve fair bits and both endpoint laws are exact.
This replaces the selected non-dyadic kernels and changes their error budgets.
The sampler functions are not yet native machine programs. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery
open Foundation.Probability
open scoped BigOperators ENNReal
noncomputable section

def forwardCounts : Fin 5 → Fin 5 → Nat :=
  ![![4096,0,0,0,0], ![2,4076,18,0,0], ![193,118,3785,0,0], ![0,0,0,4096,0], ![0,0,0,0,4096]]
def reverseCounts : Fin 5 → Fin 5 → Nat :=
  ![![3912,1,183,0,0], ![2,4001,93,0,0], ![0,1,4095,0,0], ![0,0,0,4096,0], ![0,0,0,0,4096]]

theorem forward_sum (x : Fin 5) : ∑ y, forwardCounts x y = 4096 := by
  fin_cases x <;> decide +kernel

theorem reverse_sum (x : Fin 5) : ∑ y, reverseCounts x y = 4096 := by
  fin_cases x <;> decide +kernel

def kernel (counts : Fin 5 → Fin 5 → Nat) (normal : ∀ x, ∑ y, counts x y = 4096) (x : Fin 5) : PMF (Fin 5) :=
  PMF.ofFintype (fun y => ENNReal.ofReal ((counts x y : ℝ) / 4096)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity), ← Finset.sum_div,
      ← Nat.cast_sum, normal x]
    norm_num)

theorem kernel_real (counts : Fin 5 → Fin 5 → Nat) (normal : ∀ x, ∑ y, counts x y = 4096) (x y : Fin 5) :
    (kernel counts normal x y).toReal = (counts x y : ℝ) / 4096 := ENNReal.toReal_ofReal (by positivity)

def forward := kernel forwardCounts forward_sum
def reverse := kernel reverseCounts reverse_sum

theorem forward_real (x y : Fin 5) : (forward x y).toReal = (forwardCounts x y : ℝ) / 4096 :=
  kernel_real _ _ x y

theorem reverse_real (x y : Fin 5) : (reverse x y).toReal = (reverseCounts x y : ℝ) / 4096 :=
  kernel_real _ _ x y

theorem count_sampler_law (counts : Fin 5 → Fin 5 → Nat) (normal : ∀ x, ∑ y, counts x y = 4096) (x : Fin 5) :
    (uniform (Fin 4096)).map (sampleCounts (counts x) (normal x)) = kernel counts normal x := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (((uniform (Fin 4096)).map _).apply_ne_top y)
    ((kernel counts normal x).apply_ne_top y)).mp
  rw [← FiniteKernelVariation.singleton, eventProb_map, sampleCounts_event_probability,
    ENNReal.toReal_div, kernel_real]
  norm_num

theorem kernel_realizable (counts : Fin 5 → Fin 5 → Nat) (normal : ∀ x, ∑ y, counts x y = 4096) (x : Fin 5) :
    FiniteFairSampling.Realizable 12 (kernel counts normal x) :=
  ⟨sampleCounts (counts x) (normal x), count_sampler_law counts normal x⟩

def sampleForward (x : Fin 5) (bits : Fin 12 → Bool) : Fin 5 :=
  sampleCounts (forwardCounts x) (forward_sum x) (bitIndexEquiv 12 bits)
def sampleReverse (x : Fin 5) (bits : Fin 12 → Bool) : Fin 5 :=
  sampleCounts (reverseCounts x) (reverse_sum x) (bitIndexEquiv 12 bits)

theorem forward_sample_law (x : Fin 5) : (uniform (Fin 12 → Bool)).map (sampleForward x) = forward x := by
  change (uniform (Fin 12 → Bool)).map (sampleCounts (forwardCounts x) (forward_sum x) ∘ bitIndexEquiv 12) = _
  rw [← PMF.map_comp, uniform_map_equiv]
  exact count_sampler_law _ _ x

theorem reverse_sample_law (x : Fin 5) : (uniform (Fin 12 → Bool)).map (sampleReverse x) = reverse x := by
  change (uniform (Fin 12 → Bool)).map (sampleCounts (reverseCounts x) (reverse_sum x) ∘ bitIndexEquiv 12) = _
  rw [← PMF.map_comp, uniform_map_equiv]
  exact count_sampler_law _ _ x

theorem forward_preserve : (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind forward =
    RecoveryRigidity.keyLaw RecoveryRigidity.target := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((_ : PMF (Fin 5)).apply_ne_top y) ((_ : PMF (Fin 5)).apply_ne_top y)).mp
  rw [FiniteKernelVariation.bind_real]
  simp_rw [RecoveryError.source_real, RecoveryError.target_real, forward_real]
  fin_cases y <;> norm_num [forwardCounts, RecoveryError.sourceCounts, RecoveryError.targetCounts, Fin.sum_univ_succ]

theorem reverse_preserve : (RecoveryRigidity.keyLaw RecoveryRigidity.target).bind reverse =
    RecoveryRigidity.keyLaw RecoveryRigidity.source := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((_ : PMF (Fin 5)).apply_ne_top y) ((_ : PMF (Fin 5)).apply_ne_top y)).mp
  rw [FiniteKernelVariation.bind_real]
  simp_rw [RecoveryError.source_real, RecoveryError.target_real, reverse_real]
  fin_cases y <;> norm_num [reverseCounts, RecoveryError.sourceCounts, RecoveryError.targetCounts, Fin.sum_univ_succ]

theorem forward_mismatch : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    forward PMF.pure = 6961 / 524288 := by
  unfold FiniteRecoveryError.failure
  simp only [PMF.bind_pure, FiniteRecoveryError.different_probability]
  norm_num [RecoveryError.source_real, forward_real, forwardCounts, RecoveryError.sourceCounts, Fin.sum_univ_succ]

theorem reverse_mismatch : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.target)
    reverse PMF.pure = 12499 / 1048576 := by
  unfold FiniteRecoveryError.failure
  simp only [PMF.bind_pure, FiniteRecoveryError.different_probability]
  norm_num [RecoveryError.target_real, reverse_real, reverseCounts, RecoveryError.targetCounts, Fin.sum_univ_succ]

theorem recovery_error : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    forward reverse = 13037041 / 536870912 := by
  rw [FiniteRecoveryError.failure_eq_one_sub_success]
  norm_num [RecoveryError.source_real, forward_real, reverse_real, forwardCounts, reverseCounts,
    RecoveryError.sourceCounts, Fin.sum_univ_succ]

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery
