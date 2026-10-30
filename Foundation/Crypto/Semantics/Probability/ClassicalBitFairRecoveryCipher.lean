import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecovery

/-! Local ciphertext invariants for the fair replacement kernels restore the
actual joint key/ciphertext law at the full-support source vertex. Preserving
only the key marginal would not suffice for this statement. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher
open Foundation.Probability
noncomputable section

theorem source_ciphertext (key : Fin 5) (message : Bool) :
    tableEncryptBit RecoveryRigidity.source key message = if key.val < 3 then message else !message := by
  fin_cases key <;> cases message <;> decide +kernel

theorem forward_ciphertext (message : Bool) (x y : Fin 5) (hy : y ∈ (FairRecovery.forward x).support) :
    tableEncryptBit RecoveryRigidity.source y message = tableEncryptBit RecoveryRigidity.source x message := by
  have nz : (FairRecovery.forward x y).toReal ≠ 0 := by
    intro h
    exact (PMF.mem_support_iff _ _).mp hy
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right ((FairRecovery.forward x).apply_ne_top y))
  rw [FairRecovery.forward_real] at nz
  fin_cases x <;> fin_cases y <;> norm_num [source_ciphertext,FairRecovery.forwardCounts] at *

theorem reverse_ciphertext (message : Bool) (x y : Fin 5) (hy : y ∈ (FairRecovery.reverse x).support) :
    tableEncryptBit RecoveryRigidity.source y message = tableEncryptBit RecoveryRigidity.source x message := by
  have nz : (FairRecovery.reverse x y).toReal ≠ 0 := by
    intro h
    exact (PMF.mem_support_iff _ _).mp hy
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right ((FairRecovery.reverse x).apply_ne_top y))
  rw [FairRecovery.reverse_real] at nz
  fin_cases x <;> fin_cases y <;> norm_num [source_ciphertext,FairRecovery.reverseCounts] at *

theorem roundtrip_ciphertext (message : Bool) (x y : Fin 5)
    (hy : y ∈ ((FairRecovery.forward x).bind FairRecovery.reverse).support) :
    tableEncryptBit RecoveryRigidity.source y message = tableEncryptBit RecoveryRigidity.source x message := by
  obtain ⟨middle,hf,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  exact (reverse_ciphertext message middle y hr).trans (forward_ciphertext message x middle hf)

theorem joint_roundtrip_preserve (message : Bool) :
    (tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      ((FairRecovery.forward original.1).bind FairRecovery.reverse).map (fun final => (final,original.2))) =
      tableEightBitLaw RecoveryRigidity.source message := by
  rw [RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  have each (key : Fin 5) :
      ((FairRecovery.forward key).bind FairRecovery.reverse).map
        (fun final => (final,tableEncryptBit RecoveryRigidity.source key message)) =
      ((FairRecovery.forward key).bind FairRecovery.reverse).map
        (fun final => (final,tableEncryptBit RecoveryRigidity.source final message)) := by
    change ((FairRecovery.forward key).bind FairRecovery.reverse).bind _ =
      ((FairRecovery.forward key).bind FairRecovery.reverse).bind _
    apply bind_congr_of_support
    intro final supported
    simp only [Function.comp_def]
    rw [roundtrip_ciphertext message key final supported]
  simp_rw [each]
  rw [← PMF.map_bind,← PMF.bind_bind,FairRecovery.forward_preserve,FairRecovery.reverse_preserve]

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher
