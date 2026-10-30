import Foundation.Crypto.Semantics.Machine.NativeCycleKernelSampler
import Foundation.Crypto.Logic.Polygraph.NativeContinuingFairRecovery

/-! Conditional laws and perturbation bounds for the actual locally generated
native family. Bounds concern input-weighted conditional distributions, not
just their final marginal laws. Native resources are proved by machine code. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCycleKernels
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
noncomputable section

def cleanKernel (r : Fin 95) (ciphertext : Bool) (key : Fin 5) : PMF (Fin 5) :=
  (Machine.evalConfigWithin (Machine.NativeCycleKernelSampler.cleanCode r)
    (Machine.Configuration.initial (Machine.NativeFiveStateSampler.rawInput key ciphertext)) 307).map NativeFairRecovery.observeKey

theorem clean_kernel_eq (r : Fin 95) (ciphertext : Bool) (key : Fin 5) :
    cleanKernel r ciphertext key = CycleKernels.kernel r key := by
  have h := congrArg (PMF.map NativeFairRecovery.readResult)
    (Machine.NativeCycleKernelSampler.clean_initial_law r key ciphertext)
  simp only [PMF.map_comp,Function.comp_def,NativeFairRecovery.readResult,Option.map_some,Option.getD_some] at h
  exact h.trans (PMF.map_id _)

def loopKernel (r : Fin 95) (ciphertext : Bool) (key : Fin 5) : PMF (Fin 5) :=
  (Machine.evalConfigWithin (Machine.NativeCycleKernelSampler.loopCode r)
    (Machine.Configuration.initial (Machine.NativeFiveStateSampler.rawInput key ciphertext)) 663).map NativeFairRecovery.observeKey

theorem loop_kernel_eq (r : Fin 95) (ciphertext : Bool) (key : Fin 5) :
    loopKernel r ciphertext key = (CycleKernels.kernel r key).bind FairRecovery.reverse := by
  have h := congrArg (PMF.map NativeContinuingFairRecovery.readState)
    (Machine.NativeCycleKernelSampler.loop_initial_state_law r key ciphertext)
  simp only [PMF.map_comp,Function.comp_def,Machine.NativeCleanFiveStateSampler.finish,
    NativeContinuingFairRecovery.read_finish] at h
  exact h.trans (PMF.map_id _)

theorem clean_preserves (r : Fin 95) (ciphertext : Bool) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind (cleanKernel r ciphertext) =
      RecoveryRigidity.keyLaw RecoveryRigidity.target := by
  have same : cleanKernel r ciphertext = CycleKernels.kernel r := funext (clean_kernel_eq r ciphertext)
  rw [same]
  exact CycleKernels.preserves r

theorem loop_preserves (r : Fin 95) (ciphertext : Bool) :
    (RecoveryRigidity.keyLaw RecoveryRigidity.source).bind (loopKernel r ciphertext) =
      RecoveryRigidity.keyLaw RecoveryRigidity.source := by
  have same : loopKernel r ciphertext = (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) :=
    funext (loop_kernel_eq r ciphertext)
  rw [same]
  rw [← PMF.bind_bind,CycleKernels.preserves,FairRecovery.reverse_preserve]

theorem clean_discrepancy (r : Fin 95) (ciphertext : Bool) :
    FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
      FairRecovery.forward (cleanKernel r ciphertext) = 1849 * (r.val : ℝ) / 524288 := by
  have same : cleanKernel r ciphertext = CycleKernels.kernel r := funext (clean_kernel_eq r ciphertext)
  rw [same]
  exact CycleKernels.edit_distance r

theorem loop_perturbation (r : Fin 95) (ciphertext : Bool) :
    FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
      (fun key => (FairRecovery.forward key).bind FairRecovery.reverse) (loopKernel r ciphertext) ≤
      1849 * (r.val : ℝ) / 524288 := by
  have same : loopKernel r ciphertext = (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) :=
    funext (loop_kernel_eq r ciphertext)
  rw [same]
  exact (FiniteKernelVariation.post _ FairRecovery.forward (CycleKernels.kernel r) FairRecovery.reverse).trans_eq
    (CycleKernels.edit_distance r)

theorem seed_recovery_distance :
    FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
      (fun key => (FairRecovery.forward key).bind FairRecovery.reverse) PMF.pure = 13037041 / 536870912 := by
  simp only [FiniteKernelVariation.distance,FiniteKernelVariation.variation_pure]
  simpa only [FiniteRecoveryError.failure,FiniteRecoveryError.different_probability] using FairRecovery.recovery_error

theorem loop_recovery_bound (r : Fin 95) (ciphertext : Bool) :
    FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source) (loopKernel r ciphertext) PMF.pure ≤
      13037041 / 536870912 + 1849 * (r.val : ℝ) / 524288 := by
  have triangle := FiniteKernelVariation.triangle (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    (loopKernel r ciphertext) (fun key => (FairRecovery.forward key).bind FairRecovery.reverse) PMF.pure
  rw [seed_recovery_distance] at triangle
  have bound := loop_perturbation r ciphertext
  have reverseBound : FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
      (loopKernel r ciphertext) (fun key => (FairRecovery.forward key).bind FairRecovery.reverse) ≤
      1849 * (r.val : ℝ) / 524288 := by
    rw [FiniteKernelVariation.symm]
    exact bound
  have actual : FiniteRecoveryError.failure (RecoveryRigidity.keyLaw RecoveryRigidity.source) (loopKernel r ciphertext) PMF.pure =
      FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source) (loopKernel r ciphertext) PMF.pure := by
    simp only [FiniteRecoveryError.failure,PMF.bind_pure,FiniteRecoveryError.different_probability,
      FiniteKernelVariation.distance,FiniteKernelVariation.variation_pure]
  rw [actual]
  linarith

end
end CryptoLogic.Polygraph.Experiment.NativeCycleKernels
