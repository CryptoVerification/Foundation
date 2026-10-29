import Foundation.Crypto.Logic.Polygraph.NativeRecoverableCoupling
import Foundation.Crypto.Logic.Polygraph.NativeStateRecovery

/-! Compare the old fixed-forward obstruction with the explicit alternative.
Endpoint native laws and local loss budgets stay the same. Recovery is exact
on reachable source states and one-sided; the old selected kernel is changed. -/
namespace CryptoLogic.Polygraph.Experiment.NativeRecoverable
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Machine.NativePreparedState (State)
noncomputable section

theorem forward_changed (message : Bool) (event : State → Prop) :
    stateForward message ≠ NativeState.RecoveryAudit.forward message event := by
  intro same
  apply NativeState.RecoveryAudit.no_reverse message event
  refine ⟨stateReverse message, ?_⟩
  intro s supported
  rw [← same]
  exact supported_state_recovers message s supported

theorem same_forward_budget (message : Bool) (event : State → Prop) :
    (forwardStep message event).loss =
      (NativeState.edgeTransition (sharpTableChain 0) (sharpTableChain 2) sharpTableChain_edge message event).loss := rfl

theorem same_reverse_budget (message : Bool) (event : State → Prop) :
    (reverseStep message event).loss =
      (NativeState.edgeTransition (sharpTableChain 2) (sharpTableChain 0) NativeState.RoundtripAudit.reverse_edge message event).loss := rfl

theorem exists_repaired_state_kernels (message : Bool) (event : State → Prop) :
    ∃ (forward reverse : State → PMF State),
      (NativeState.nativeLaw (sharpTableChain 0) message).bind forward = NativeState.nativeLaw (sharpTableChain 2) message ∧
      (NativeState.nativeLaw (sharpTableChain 2) message).bind reverse = NativeState.nativeLaw (sharpTableChain 0) message ∧
      KernelRecovery.RecoversOn forward reverse (fun s => s ∈ (NativeState.nativeLaw (sharpTableChain 0) message).support) ∧
      forward ≠ NativeState.RecoveryAudit.forward message event :=
  ⟨stateForward message, stateReverse message, state_forward_preserves message, state_reverse_preserves message,
    supported_state_recovers message, forward_changed message event⟩

end
end CryptoLogic.Polygraph.Experiment.NativeRecoverable
