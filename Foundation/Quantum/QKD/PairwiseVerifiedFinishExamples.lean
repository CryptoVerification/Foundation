import Foundation.Quantum.QKD.PairwiseVerifiedFinish

/-! A coherent three-signal attack with two selected positions and one
unmatched position. This is a supported-state test, not a positive key rate. -/
namespace Foundation.Quantum.QKD.PairwiseVerifiedFinishExamples
noncomputable section
open PairwisePhaseCoordinates PairwiseExpandedVerification
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

def positions : Finset (Fin 3) := {0,2}

theorem selected_count : BB84SiftedInput.selectedCount positions = 2 := by decide

theorem unmatched_count : BB84SiftedInput.remainderCount positions = 1 := by decide

instance : NeZero (BB84SiftedInput.selectedCount positions) := ⟨by rw [selected_count]; decide⟩

def configuration : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount positions) :=
  (fun _ => 0, {0})

def attack : BlockAttack 3 (qubits 3) :=
  Channel.ofIsometry (Op.copy (qubits 3)) (by
    change Op.seq (Op.copy (qubits 3)) (Op.dagger (Op.copy (qubits 3))) = Op.ident (qubits 3)
    exact Op.copy_special _)

theorem support_count : acceptedSupport 1 0 1 0 configuration = 1 := by
  simp only [acceptedSupport, phaseSet_band, BB84DelayedDecision.accepts,
    errorCode, Equiv.symm_apply_apply]
  decide

theorem coefficient : bound 1 0 1 0 configuration = 1/4 := by
  unfold bound
  rw [support_count, selected_count]
  norm_num

/-- Both seeds have the original three-position type, while the phase
certificate has two selected positions. One unmatched signal is discarded. -/
theorem full_position_physical : OperatorApprox
    (Subnormalized.joint (VerifiedHash.fromDensity (tag := 1) (length := 1)
      (restoredRaw attack positions (fun _ => .Z) 1 0 1 0 configuration)))
    (Subnormalized.joint (CommonKey.uniformize (VerifiedHash.fromDensity (tag := 1) (length := 1)
      (restoredRaw attack positions (fun _ => .Z) 1 0 1 0 configuration)))) (1/2) := by
  have h := finished_verified_physical_secrecy (tag := 1) (length := 1)
    attack positions (fun _ => .Z) 1 0 1 0 configuration
  convert h using 1
  rw [privacyError, coefficient, show configuration.2.card = 1 by decide]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseVerifiedFinishExamples
