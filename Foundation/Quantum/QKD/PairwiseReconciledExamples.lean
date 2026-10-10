import Foundation.Quantum.QKD.PairwiseReconciledPublished

/-! The actual supported-state corrected/verified public experiment for a
coherent four-signal attack. Three remaining bits disclose two parities; this
fixed-configuration example is not a full-protocol useful-key theorem. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledExamples
noncomputable section
open PairwisePhaseCoordinates PairwiseReconciledVerification
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def attack : BlockAttack 4 (qubits 4) :=
  Channel.ofIsometry (Op.copy (qubits 4)) (by
    change Op.seq (Op.copy (qubits 4)) (Op.dagger (Op.copy (qubits 4))) = Op.ident (qubits 4)
    exact Op.copy_special _)

def configuration : PairwiseSampling.Configuration 4 := (fun _ => 0,{0})

theorem support_count : acceptedSupport 1 0 1 0 configuration = 1 := by
  simp only [acceptedSupport, phaseSet_band, BB84DelayedDecision.accepts,
    errorCode, Equiv.symm_apply_apply]
  decide

theorem support_coefficient : bound 1 0 1 0 configuration = 1/16 := by
  norm_num [bound, support_count]

theorem disclosure_coefficient : coefficient 1 1 0 1 0 configuration = 1 := by
  rw [coefficient_public_bits, support_coefficient]
  norm_num [configuration, BB84SiftedInput.remainderCount, BB84SiftedInput.selectedCount,
    ArbitraryReconciliation.publicBits, IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

theorem corrected_verified_public : OperatorApprox
    (Subnormalized.joint (finishedPublished (tag := 1) (length := 1) (n := 4)
      attack Finset.univ 1 0 1 0 configuration))
    (Subnormalized.joint (CommonKey.uniformize (finishedPublished (tag := 1) (length := 1) (n := 4)
      attack Finset.univ 1 0 1 0 configuration))) (1/2) := by
  have h := finished_published_secrecy (tag := 1) (length := 1) (n := 4)
    attack Finset.univ 1 0 1 0 configuration
  convert h using 1
  rw [privacyError, disclosure_coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseReconciledExamples
