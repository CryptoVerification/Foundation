import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryErrorCertificate
import Foundation.Crypto.Semantics.Probability.FiniteRecoveryError
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryRigidity

/-! A sharp, uniform 3/256 recovery-error lower bound on the full-support
five-state edge. This includes arbitrary stochastic forward/reverse kernels.
Sharpness does not require the reverse marginal to be preserved. The attaining
maximal coupling is semantic; no bounded sampler is claimed. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError
open Foundation.Probability
open scoped BigOperators ENNReal
noncomputable section

theorem source_real (key : Fin 5) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.source key).toReal = (sourceCounts key : ℝ) / 256 := by
  rw [RecoveryRigidity.key_atom,RecoveryRigidity.source_counts]
  simp [sourceCounts,ENNReal.toReal_div]

theorem target_real (key : Fin 5) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.target key).toReal = (targetCounts key : ℝ) / 256 := by
  rw [RecoveryRigidity.key_atom,RecoveryRigidity.target_counts]
  simp [targetCounts,ENNReal.toReal_div]

theorem capacity_eq (decoder : Fin 5 → Fin 5) :
    FiniteRecoveryError.capacity
      (fun key => (RecoveryRigidity.keyLaw RecoveryRigidity.source key).toReal)
      (fun key => (RecoveryRigidity.keyLaw RecoveryRigidity.target key).toReal) decoder =
        (retainedCounts decoder : ℝ) / 256 := by
  have assigned (a : Fin 5) :
      (∑ b, if decoder b = a then (RecoveryRigidity.keyLaw RecoveryRigidity.target b).toReal else 0) =
        (assignedCounts decoder a : ℝ) / 256 := by
    simp only [target_real, assignedCounts, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  unfold FiniteRecoveryError.capacity
  simp_rw [source_real,assigned,min_div_div_right (by norm_num : (0 : ℝ) ≤ 256)]
  rw [← Finset.sum_div]
  simp only [retainedCounts,Nat.cast_sum,Nat.cast_min]

theorem capacity_bound (decoder : Fin 5 → Fin 5) :
    FiniteRecoveryError.capacity
      (fun key => (RecoveryRigidity.keyLaw RecoveryRigidity.source key).toReal)
      (fun key => (RecoveryRigidity.keyLaw RecoveryRigidity.target key).toReal) decoder ≤ 253 / 256 := by
  rw [capacity_eq]
  have h : (retainedCounts decoder : ℝ) ≤ 253 := by exact_mod_cast all_decoder_counts decoder
  linarith

theorem recovery_error_lower (forward reverse : Fin 5 → PMF (Fin 5))
    (preserve : (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind forward =
      RecoveryRigidity.keyLaw RecoveryRigidity.target) :
    3 / 256 ≤ FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source) forward reverse := by
  have h := FiniteRecoveryError.failure_lower (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    (RecoveryRigidity.keyLaw RecoveryRigidity.target) forward reverse preserve (253 / 256) capacity_bound
  linarith

theorem variation : finiteVariation (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    (RecoveryRigidity.keyLaw RecoveryRigidity.target) = 3 / 256 := by
  norm_num [finiteVariation,source_real,target_real,sourceCounts,targetCounts,Fin.sum_univ_succ]

def attainingForward : Fin 5 → PMF (Fin 5) := FiniteMaximalCoupling.kernel
  (RecoveryRigidity.keyLaw RecoveryRigidity.source) (RecoveryRigidity.keyLaw RecoveryRigidity.target)

theorem attaining_preserve : (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind attainingForward =
    RecoveryRigidity.keyLaw RecoveryRigidity.target := FiniteMaximalCoupling.kernel_preserve _ _

theorem attaining_error : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    attainingForward (fun key => PMF.pure key) = 3 / 256 := by
  rw [FiniteRecoveryError.failure_identity_joint,attainingForward,FiniteMaximalCoupling.kernel_joint,
    FiniteMaximalCoupling.mismatch_probability,variation]
  norm_num

theorem attaining_reverse_not_preserve :
    (RecoveryRigidity.keyLaw RecoveryRigidity.target).bind (fun key => PMF.pure key) ≠
      RecoveryRigidity.keyLaw RecoveryRigidity.source := by
  rw [PMF.bind_pure]
  intro same
  exact RecoveryRigidity.unmatched_atom 0
    (congrArg (fun law : PMF (Fin 5) => (law 0).toReal) same.symm)

def preservingReverse : Fin 5 → PMF (Fin 5) := FiniteMaximalCoupling.kernel
  (RecoveryRigidity.keyLaw RecoveryRigidity.target) (RecoveryRigidity.keyLaw RecoveryRigidity.source)

theorem reverse_preserves : (RecoveryRigidity.keyLaw RecoveryRigidity.target).bind preservingReverse =
    RecoveryRigidity.keyLaw RecoveryRigidity.source := FiniteMaximalCoupling.kernel_preserve _ _

theorem maximal_real (p q : PMF (Fin 5)) (nonzero : ∀ x, (p x).toReal ≠ 0) (x y : Fin 5) :
    (FiniteMaximalCoupling.kernel p q x y).toReal = FiniteMaximalCoupling.mass p q x y / (p x).toReal := by
  simp only [FiniteMaximalCoupling.kernel, dif_neg (nonzero x), PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (div_nonneg (FiniteMaximalCoupling.mass_nonneg p q x y) ENNReal.toReal_nonneg)

theorem forward_matrix (x y : Fin 5) : (attainingForward x y).toReal =
    ![![1,0,0,0,0],![0,1,0,0,0],![1/21,1/42,13/14,0,0],![0,0,0,1,0],![0,0,0,0,1]] x y := by
  have hp (i : Fin 5) : (RecoveryRigidity.keyLaw RecoveryRigidity.source i).toReal ≠ 0 := by
    rw [source_real]
    fin_cases i <;> norm_num [sourceCounts]
  rw [attainingForward,maximal_real _ _ hp]
  fin_cases x <;> fin_cases y <;>
    norm_num [FiniteMaximalCoupling.mass, FiniteMaximalCoupling.common, FiniteMaximalCoupling.left,
      FiniteMaximalCoupling.right, FiniteMaximalCoupling.residual,
      source_real,target_real,sourceCounts,targetCounts,Fin.sum_univ_succ,Fin.ext_iff]

theorem reverse_matrix (x y : Fin 5) : (preservingReverse x y).toReal =
    ![![43/45,0,2/45,0,0],![0,43/44,1/44,0,0],![0,0,1,0,0],![0,0,0,1,0],![0,0,0,0,1]] x y := by
  have hq (i : Fin 5) : (RecoveryRigidity.keyLaw RecoveryRigidity.target i).toReal ≠ 0 := by
    rw [target_real]
    fin_cases i <;> norm_num [targetCounts]
  rw [preservingReverse,maximal_real _ _ hq]
  fin_cases x <;> fin_cases y <;>
    norm_num [FiniteMaximalCoupling.mass, FiniteMaximalCoupling.common, FiniteMaximalCoupling.left,
      FiniteMaximalCoupling.right, FiniteMaximalCoupling.residual,
      source_real,target_real,sourceCounts,targetCounts,Fin.sum_univ_succ,Fin.ext_iff]

theorem preserving_error : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    attainingForward preservingReverse = 5719 / 253440 := by
  rw [FiniteRecoveryError.failure_eq_one_sub_success]
  norm_num [forward_matrix,reverse_matrix,source_real,sourceCounts,Fin.sum_univ_succ]

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError
