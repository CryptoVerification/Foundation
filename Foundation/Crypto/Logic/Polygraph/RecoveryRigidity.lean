import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryRigidity
import Foundation.Crypto.Semantics.Probability.RecoveryViewTransport
import Foundation.Crypto.Semantics.Machine.NativePreparedState
import Foundation.Crypto.Logic.Polygraph.GameCoherence

/-! The grid obstruction applies to arbitrary full-cell state kernels, and
to arbitrary game paths through the specified full-support intermediate
endpoint. This rules out uniform exact-recovery cells without constraining
the coupling to the earlier chosen maximal kernel. -/
namespace CryptoLogic.Polygraph.Experiment.RecoveryRigidity
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

def stateView (pc : ℕ) (v : OrderedGridVertex 32) (message : Bool) (key : Fin 5) : Machine.NativePreparedState.State :=
  Machine.NativePreparedState.state (Machine.NativePreparedState.finish pc (key,tableEncryptBit v key message))

def readState (state : Machine.NativePreparedState.State) : Fin 5 := (Machine.NativePreparedState.decode state).1

theorem state_view_inverse (pc : ℕ) (v : OrderedGridVertex 32) (message : Bool) :
    Function.LeftInverse readState (stateView pc v message) := by
  intro key
  change ((Machine.NativePreparedInternalResult.observe
    (Machine.NativePreparedState.finish pc (key,tableEncryptBit v key message))).getD (0,false)).1 = key
  rw [Machine.NativePreparedState.observe_finish]
  rfl

theorem native_endpoint_law (v : OrderedGridVertex 32) (message : Bool) :
    (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
      (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map
        Machine.NativePreparedState.state =
      (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw v).map (stateView
        (Machine.NativePreparedKeyDecision.preparation.length + Machine.NativePreparedKeyDecision.source.length + 2) v message) := by
  rw [Machine.NativePreparedState.initial_law, Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor, PMF.map_comp]
  rfl

theorem no_full_state_exact_recovery (sourcePc targetPc : ℕ) (message : Bool) :
    ¬ ∃ (forward reverse : Machine.NativePreparedState.State → PMF Machine.NativePreparedState.State),
      ((Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source).map
        (stateView sourcePc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)).bind forward =
      (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target).map
        (stateView targetPc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target message) ∧
      ∀ key, (forward (stateView sourcePc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message key)).bind reverse =
        PMF.pure (stateView sourcePc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message key) := by
  rintro ⟨forward,reverse,preserve,recovers⟩
  let sourceView := stateView sourcePc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message
  let targetView := stateView targetPc Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target message
  have finite_preserve := RecoveryViewTransport.induced_preserves
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source)
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target)
    sourceView targetView readState (state_view_inverse targetPc _ message) forward preserve
  have finite_recover := RecoveryViewTransport.induced_recovers
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source)
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target)
    sourceView targetView readState readState (state_view_inverse sourcePc _ message)
    (state_view_inverse targetPc _ message) forward reverse Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source_full preserve recovers
  exact Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.no_exact_recoverable_transport
    ⟨RecoveryViewTransport.forward sourceView readState forward,
      RecoveryViewTransport.reverse targetView readState reverse,finite_preserve,finite_recover⟩

def sourceGame (sourceEvent : Fin 5 → Prop) : Observed :=
  ⟨Fin 5,.sample (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source),sourceEvent⟩

def targetGame (targetEvent : Fin 5 → Prop) : Observed :=
  ⟨Fin 5,.sample (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target),targetEvent⟩

theorem no_path_recovery (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (sourceGame sourceEvent) (targetGame targetEvent))
    (reverse : Path (targetGame targetEvent) (sourceGame sourceEvent)) :
    ¬ ∀ key, (Path.seq forward reverse).kernel key = PMF.pure key := by
  intro recovers
  apply Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.no_exact_recoverable_transport
  exact ⟨forward.kernel,reverse.kernel,forward.preserve,recovers⟩

theorem no_identity_cell (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (sourceGame sourceEvent) (targetGame targetEvent))
    (reverse : Path (targetGame targetEvent) (sourceGame sourceEvent)) :
    IsEmpty (Cell4 (Path.seq forward reverse) (Path.identity (sourceGame sourceEvent))) := by
  constructor
  intro cell
  exact no_path_recovery sourceEvent targetEvent forward reverse cell.sound.kernel_eq

theorem no_stationary_cell (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (sourceGame sourceEvent) (targetGame targetEvent))
    (reverse : Path (targetGame targetEvent) (sourceGame sourceEvent))
    (stationary : Path (sourceGame sourceEvent) (sourceGame sourceEvent))
    (identity_kernel : ∀ key, stationary.kernel key = PMF.pure key) :
    IsEmpty (Cell4 (Path.seq forward reverse) stationary) := by
  constructor
  intro cell
  apply no_path_recovery sourceEvent targetEvent forward reverse
  intro key
  exact (cell.sound.kernel_eq key).trans (identity_kernel key)

end
end CryptoLogic.Polygraph.Experiment.RecoveryRigidity
