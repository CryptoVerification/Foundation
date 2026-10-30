import Foundation.Crypto.Semantics.Machine.NativeFairRecoverySampler
import Foundation.Crypto.Logic.Polygraph.FairRecovery

/-! Each local kernel in the new finite game paths is realized by its native
143-step sampler. This does not connect the two samplers into one machine
execution or erase the private request/coin history. -/
namespace CryptoLogic.Polygraph.Experiment.NativeFairRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
noncomputable section

def readResult (result : Option (Fin 5 × Bool)) : Fin 5 := (result.map Prod.fst).getD 0

def observeKey (state : Machine.Configuration) : Fin 5 := readResult (Machine.NativeEightBitCipher.observe state)

def nativeKernel (backward ciphertext : Bool) (key : Fin 5) : PMF (Fin 5) :=
  (Machine.evalConfigWithin (Machine.NativeFairRecoverySampler.code backward)
    (Machine.Configuration.initial (Machine.NativeFairRecoverySampler.rawInput key ciphertext)) 143).map observeKey

theorem kernel_eq (backward ciphertext : Bool) (key : Fin 5) :
    nativeKernel backward ciphertext key = Machine.NativeFairRecoverySampler.kernel backward key := by
  have h := congrArg (PMF.map readResult) (Machine.NativeFairRecoverySampler.initial_law backward key ciphertext)
  simp only [PMF.map_comp, Function.comp_def, readResult, Option.map_some, Option.getD_some] at h
  exact h.trans (PMF.map_id _)

theorem forward_realized (event : Fin 5 → Prop) (ciphertext : Bool) :
    (FairRecoveryGame.forward event).kernel = nativeKernel false ciphertext := by
  funext key
  rw [kernel_eq]
  rfl

theorem reverse_realized (event : Fin 5 → Prop) (ciphertext : Bool) :
    (FairRecoveryGame.reverse event).kernel = nativeKernel true ciphertext := by
  funext key
  rw [kernel_eq]
  rfl

theorem forward_preserves (ciphertext : Bool) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind (nativeKernel false ciphertext) =
      RecoveryRigidity.keyLaw RecoveryRigidity.target := by
  have same : nativeKernel false ciphertext = FairRecovery.forward := funext (kernel_eq false ciphertext)
  rw [same]
  exact FairRecovery.forward_preserve

theorem reverse_preserves (ciphertext : Bool) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.target).bind (nativeKernel true ciphertext) =
      RecoveryRigidity.keyLaw RecoveryRigidity.source := by
  have same : nativeKernel true ciphertext = FairRecovery.reverse := funext (kernel_eq true ciphertext)
  rw [same]
  exact FairRecovery.reverse_preserve

end
end CryptoLogic.Polygraph.Experiment.NativeFairRecovery
