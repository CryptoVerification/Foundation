import Foundation.Crypto.Semantics.Machine.NativeContinuingFairRecovery
import Foundation.Crypto.Logic.Polygraph.NativeFairRecovery

/-! The finite game roundtrip kernel is observed from one 663-step native
execution, including request adaptation and both physical history erasures.
The entry is a four-bit conditional request. The original reference-cipher
caller and a matching native stationary comparator are separate contracts. -/
namespace CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
noncomputable section

def readState : Machine.NativePreparedState.State → Fin 5 :=
  Quotient.lift NativeFairRecovery.observeKey (by
    intro c d h
    unfold NativeFairRecovery.observeKey
    rw [Machine.NativeControlledCipherInitial.observe_equivalent c d h])

theorem read_finish (pc : Nat) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Machine.Tape) :
    readState (Machine.NativePreparedState.state (Machine.NativeCleanFairRecovery.finish pc key ciphertext inputSuffix outputSuffix)) = key := by
  change NativeFairRecovery.readResult (Machine.NativeEightBitCipher.observe
    (Machine.NativeCleanFairRecovery.finish pc key ciphertext inputSuffix outputSuffix)) = _
  rw [Machine.NativeCleanFairRecovery.observe_finish]
  rfl

def nativeKernel (ciphertext : Bool) (key : Fin 5) : PMF (Fin 5) :=
  (Machine.evalConfigWithin Machine.NativeContinuingFairRecovery.code
    (Machine.Configuration.initial (Machine.NativeFairRecoverySampler.rawInput key ciphertext)) 663).map NativeFairRecovery.observeKey

theorem kernel_eq (ciphertext : Bool) (key : Fin 5) :
    nativeKernel ciphertext key = (FairRecovery.forward key).bind FairRecovery.reverse := by
  have h := congrArg (PMF.map readState) (Machine.NativeContinuingFairRecovery.initial_state_law key ciphertext)
  simp only [PMF.map_comp,Function.comp_def,read_finish] at h
  exact h.trans (PMF.map_id _)

theorem game_path_realized (event : Fin 5 → Prop) (ciphertext : Bool) :
    (FairRecoveryGame.roundtrip event).kernel = nativeKernel ciphertext := by
  funext key
  rw [kernel_eq]
  rfl

theorem recovery_error (ciphertext : Bool) :
    FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source) (nativeKernel ciphertext) PMF.pure =
      13037041 / 536870912 := by
  simpa only [FiniteRecoveryError.failure,PMF.bind_pure,kernel_eq] using FairRecovery.recovery_error

end
end CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery
