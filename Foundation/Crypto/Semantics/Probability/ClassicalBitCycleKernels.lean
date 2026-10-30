import Foundation.Crypto.Semantics.Probability.FairCycleRelations
import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecoveryCipher

/-! Ninety-five distinct twelve-bit kernels constructed by local edits of the
existing five-state cryptographic kernel. Endpoint and joint ciphertext laws
follow from local certificates. No improvement in recovery error is claimed. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels
open Foundation.Probability IntegerKernelCycles
open scoped BigOperators
noncomputable section

def base : Fin 5 → Fin 5 → ℤ := signed FairRecovery.forwardCounts

theorem seed_kernel : FiniteFairKernelCertificate.kernel 12 FairRecovery.forwardCounts
    (by simpa using FairRecovery.forward_sum) = FairRecovery.forward := by rfl

theorem base_certificate : Certificate RecoveryError.sourceCounts RecoveryError.targetCounts (2 ^ 12) base := by
  apply Certificate.ofNat _ _ _ FairRecovery.forwardCounts
    (by simpa using FairRecovery.forward_sum)
  apply FiniteFairKernelCertificate.columns_of_preserve 12 256 (by decide)
    (RecoveryRigidity.keyLaw RecoveryRigidity.source) (RecoveryRigidity.keyLaw RecoveryRigidity.target)
    RecoveryError.sourceCounts RecoveryError.targetCounts FairRecovery.forwardCounts
    (by simpa using FairRecovery.forward_sum) RecoveryError.source_real RecoveryError.target_real
  rw [seed_kernel]
  exact FairRecovery.forward_preserve

def edited (r : Fin 95) : Fin 5 → Fin 5 → ℤ :=
  applyCycle RecoveryError.sourceCounts base 0 1 0 1 (-(r.val : ℤ))

theorem corner00 (r : Fin 95) : edited r 0 0 = 4096 - 43 * (r.val : ℤ) := by
  change (4096 : ℤ) + -(r.val : ℤ) * (43 - 0) * (1 - 0) = _
  ring

theorem corner01 (r : Fin 95) : edited r 0 1 = 43 * (r.val : ℤ) := by
  change (0 : ℤ) + -(r.val : ℤ) * (43 - 0) * (0 - 1) = _
  ring

theorem corner10 (r : Fin 95) : edited r 1 0 = 2 + 43 * (r.val : ℤ) := by
  change (2 : ℤ) + -(r.val : ℤ) * (0 - 43) * (1 - 0) = _
  ring

theorem corner11 (r : Fin 95) : edited r 1 1 = 4076 - 43 * (r.val : ℤ) := by
  change (4076 : ℤ) + -(r.val : ℤ) * (0 - 43) * (0 - 1) = _
  ring

def move (r : Fin 95) : Move RecoveryError.sourceCounts base (edited r) where
  i := 0
  j := 1
  k := 0
  l := 1
  coefficient := -(r.val : ℤ)
  equation := rfl
  corner00 := by rw [corner00]; have := r.isLt; omega
  corner01 := by rw [corner01]; positivity
  corner10 := by rw [corner10]; positivity
  corner11 := by rw [corner11]; have := r.isLt; omega

def path (r : Fin 95) : Path RecoveryError.sourceCounts base (edited r) := .step (move r)

theorem certificate (r : Fin 95) : Certificate RecoveryError.sourceCounts RecoveryError.targetCounts (2 ^ 12) (edited r) :=
  (path r).sound base_certificate

def kernel (r : Fin 95) : Fin 5 → PMF (Fin 5) := FairCycleKernel.pathKernel 12 base_certificate (path r)

theorem realizable (r : Fin 95) (a : Fin 5) : FiniteFairSampling.Realizable 12 (kernel r a) :=
  FairCycleKernel.path_realizable 12 base_certificate (path r) a

theorem preserves (r : Fin 95) : (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind (kernel r) =
    RecoveryRigidity.keyLaw RecoveryRigidity.target :=
  FairCycleKernel.path_preserves 12 256 (by decide) base_certificate (path r) _ _
    RecoveryError.source_real RecoveryError.target_real

theorem entry01 (r : Fin 95) : (kernel r 0 1).toReal = 43 * (r.val : ℝ) / 4096 := by
  change (FiniteFairKernelCertificate.kernel 12 (natural (edited r)) (certificate r).natural_rows 0 1).toReal = _
  rw [FiniteFairKernelCertificate.kernel_real]
  have count : natural (edited r) 0 1 = 43 * r.val := by
    have h := (certificate r).natural_cast 0 1
    rw [corner01] at h
    exact_mod_cast h
  rw [count]
  push_cast
  norm_num

theorem kernel_injective : Function.Injective kernel := by
  intro r s equal
  have h := congrArg (fun k : Fin 5 → PMF (Fin 5) => (k 0 1).toReal) equal
  rw [entry01,entry01] at h
  have cast : (r.val : ℝ) = (s.val : ℝ) := by linarith
  apply Fin.ext
  exact_mod_cast cast

theorem base_kernel : FairCycleKernel.kernel 12 base_certificate = FairRecovery.forward := by
  funext a
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' ((_ : PMF (Fin 5)).apply_ne_top b)
    ((FairRecovery.forward a).apply_ne_top b)).mp
  change (FiniteFairKernelCertificate.kernel 12 (natural base) base_certificate.natural_rows a b).toReal = _
  rw [FiniteFairKernelCertificate.kernel_real,FairRecovery.forward_real]
  simp [natural,base,signed]

theorem base_ciphertext (message : Bool) (a b : Fin 5) (nonzero : base a b ≠ 0) :
    tableEncryptBit RecoveryRigidity.source b message = tableEncryptBit RecoveryRigidity.source a message := by
  apply FairRecoveryCipher.forward_ciphertext message a b
  rw [← base_kernel]
  exact (FairCycleKernel.support_iff_table_nonzero 12 base_certificate a b).mpr nonzero

theorem path_respects (r : Fin 95) (message : Bool) :
    Respects (fun a b => tableEncryptBit RecoveryRigidity.source b message =
      tableEncryptBit RecoveryRigidity.source a message) (path r) := by
  simp [Respects,path,move,FairRecoveryCipher.source_ciphertext]

theorem ciphertext (r : Fin 95) (message : Bool) (a b : Fin 5) (supported : b ∈ (kernel r a).support) :
    tableEncryptBit RecoveryRigidity.source b message = tableEncryptBit RecoveryRigidity.source a message := by
  apply (path r).relation _ (base_ciphertext message) (path_respects r message) a b
  exact FairCycleKernel.support_table_nonzero 12 (certificate r) a b supported

theorem target_ciphertext (key : Fin 5) (message : Bool) :
    tableEncryptBit RecoveryRigidity.target key message = tableEncryptBit RecoveryRigidity.source key message := by
  fin_cases key <;> cases message <;> decide +kernel

theorem joint_preserves (r : Fin 95) (message : Bool) :
    (tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      (kernel r original.1).map (fun final => (final,original.2))) =
      tableEightBitLaw RecoveryRigidity.target message := by
  rw [RecoveryRigidity.joint_law_factor,RecoveryRigidity.joint_law_factor]
  simp_rw [target_ciphertext]
  exact FairCycleKernel.path_joint_preserves 12 256 (by decide) base_certificate (path r) _ _
    RecoveryError.source_real RecoveryError.target_real
    (fun key => tableEncryptBit RecoveryRigidity.source key message)
    (fun key => tableEncryptBit RecoveryRigidity.source key message)
    (base_ciphertext message) (path_respects r message)

theorem edit_distance (r : Fin 95) :
    FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
      FairRecovery.forward (kernel r) = 1849 * (r.val : ℝ) / 524288 := by
  rw [← base_kernel]
  change FiniteKernelVariation.distance _ (FairCycleKernel.kernel 12 base_certificate)
    (FairCycleKernel.kernel 12 (certificate r)) = _
  rw [FairCycleKernel.distance_eq]
  simp only [RecoveryError.source_real]
  norm_num [Fin.sum_univ_succ,base,signed,edited,applyCycle,cycle,rowWeight,direction,
    FairRecovery.forwardCounts,RecoveryError.sourceCounts]
  simp only [show (2 : Fin 5) ≠ 1 by decide, show Fin.succ (2 : Fin 4) ≠ (1 : Fin 5) by decide,
    show (Fin.succ (Fin.succ (2 : Fin 3))) ≠ (1 : Fin 5) by decide, if_false, abs_zero,mul_zero,add_zero]
  ring

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels
