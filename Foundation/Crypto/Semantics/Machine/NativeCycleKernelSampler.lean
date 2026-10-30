import Foundation.Crypto.Semantics.Machine.NativeContinuingFiveStateSampler
import Foundation.Crypto.Semantics.Machine.NativeCertifiedFiveStateKernel
import Foundation.Crypto.Semantics.Probability.ClassicalBitCycleKernels

/-! Uniform native realization of the locally constructed 95-kernel family.
Each parameter chooses a fixed program; the parameter is not an uncharged
runtime input. Single clean sampling preserves the full joint ciphertext law.
Two-stage execution uses the existing reverse sampler and charges the adapter. -/
namespace Machine.NativeCycleKernelSampler
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Foundation.Probability.IntegerKernelCycles

def draw (r : Fin 95) (key : Fin 5) (coins : Fin 12 → Bool) : Fin 5 :=
  NativeCertifiedFiveStateKernel.draw (CycleKernels.certificate r) key coins

theorem draw_law (r : Fin 95) (key : Fin 5) :
    (uniform (Fin 12 → Bool)).map (draw r key) = CycleKernels.kernel r key :=
  NativeCertifiedFiveStateKernel.draw_law (CycleKernels.certificate r) key

theorem kernel_eq (r : Fin 95) : NativeFiveStateSampler.kernel (draw r) = CycleKernels.kernel r :=
  funext (draw_law r)

def cleanCode (r : Fin 95) : Program := NativeCleanFiveStateSampler.code (draw r)

theorem clean_stops (r : Fin 95) : StopsEverywhere (cleanCode r) 307 :=
  NativeCleanFiveStateSampler.stops (draw r)

theorem clean_length (r : Fin 95) : (cleanCode r).length ≤ 985484 :=
  NativeCleanFiveStateSampler.code_length (draw r)

theorem clean_full_run (r : Fin 95) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (cleanCode r) (NativeFiveStateSampler.entry key ciphertext inputSuffix outputSuffix) 307 =
      (CycleKernels.kernel r key).map (fun result => NativeCleanFiveStateSampler.finish
        ((NativeFiveStateSampler.code (draw r)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
        result ciphertext inputSuffix outputSuffix) := by
  rw [cleanCode,NativeCleanFiveStateSampler.full_run,kernel_eq]

theorem clean_initial_state_law (r : Fin 95) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (cleanCode r) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 307).map
      NativePreparedState.state = (CycleKernels.kernel r key).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish
          ((NativeFiveStateSampler.code (draw r)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
          result ciphertext {} {})) := by
  rw [cleanCode,NativeCleanFiveStateSampler.initial_state_law,kernel_eq]

theorem clean_initial_law (r : Fin 95) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (cleanCode r) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 307).map
      NativeEightBitCipher.observe = (CycleKernels.kernel r key).map (fun result => some (result,ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFiveStateSampler.entry_equivalent key ciphertext).symm
    307 _ NativeControlledCipherInitial.observe_equivalent]
  rw [cleanCode,NativeCleanFiveStateSampler.framed_law,kernel_eq]

theorem clean_joint_observed (r : Fin 95) (message : Bool) :
    ((tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      evalConfigWithin (cleanCode r) (Configuration.initial (NativeFiveStateSampler.rawInput original.1 original.2)) 307)).map
        NativeEightBitCipher.observe = (tableEightBitLaw RecoveryRigidity.target message).map some := by
  rw [PMF.map_bind]
  simp_rw [clean_initial_law]
  have h := congrArg (PMF.map some) (CycleKernels.joint_preserves r message)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def] using h

theorem clean_joint_state_law (r : Fin 95) (message : Bool) :
    ((tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      evalConfigWithin (cleanCode r) (Configuration.initial (NativeFiveStateSampler.rawInput original.1 original.2)) 307)).map
        NativePreparedState.state = (tableEightBitLaw RecoveryRigidity.target message).map (fun final => NativePreparedState.state
          (NativeCleanFiveStateSampler.finish
            ((NativeFiveStateSampler.code (draw r)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
            final.1 final.2 {} {})) := by
  rw [PMF.map_bind]
  simp_rw [clean_initial_state_law]
  have h := congrArg (PMF.map (fun final : Fin 5 × Bool => NativePreparedState.state
    (NativeCleanFiveStateSampler.finish
      ((NativeFiveStateSampler.code (draw r)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
      final.1 final.2 {} {}))) (CycleKernels.joint_preserves r message)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def] using h

def loopCode (r : Fin 95) : Program := NativeContinuingFiveStateSampler.code (draw r) FairRecovery.sampleReverse

theorem reverse_kernel : NativeFiveStateSampler.kernel FairRecovery.sampleReverse = FairRecovery.reverse :=
  funext FairRecovery.reverse_sample_law

theorem loop_stops (r : Fin 95) : StopsEverywhere (loopCode r) 663 :=
  NativeContinuingFiveStateSampler.stops (draw r) FairRecovery.sampleReverse

theorem loop_length (r : Fin 95) : (loopCode r).length ≤ 1971259 :=
  NativeContinuingFiveStateSampler.code_length (draw r) FairRecovery.sampleReverse

theorem loop_initial_state_law (r : Fin 95) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (loopCode r) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 663).map
      NativePreparedState.state = ((CycleKernels.kernel r key).bind FairRecovery.reverse).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish
          ((NativeCleanFiveStateSampler.code (draw r)).length +
            (NativeContinuingFiveStateSampler.nextCode FairRecovery.sampleReverse).length + 2)
          result ciphertext {left := List.replicate 19 none} {left := [none]})) := by
  rw [loopCode,NativeContinuingFiveStateSampler.initial_state_law,kernel_eq,reverse_kernel]

theorem loop_ciphertext (r : Fin 95) (message : Bool) (key final : Fin 5)
    (supported : final ∈ ((CycleKernels.kernel r key).bind FairRecovery.reverse).support) :
    tableEncryptBit RecoveryRigidity.source final message = tableEncryptBit RecoveryRigidity.source key message := by
  obtain ⟨middle,first,second⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  exact (FairRecoveryCipher.reverse_ciphertext message middle final second).trans
    (CycleKernels.ciphertext r message key middle first)

theorem loop_joint_preserves (r : Fin 95) (message : Bool) :
    (tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      ((CycleKernels.kernel r original.1).bind FairRecovery.reverse).map (fun final => (final,original.2))) =
      tableEightBitLaw RecoveryRigidity.source message := by
  rw [RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  have each (key : Fin 5) : ((CycleKernels.kernel r key).bind FairRecovery.reverse).map
      (fun final => (final,tableEncryptBit RecoveryRigidity.source key message)) =
      ((CycleKernels.kernel r key).bind FairRecovery.reverse).map
        (fun final => (final,tableEncryptBit RecoveryRigidity.source final message)) := by
    change ((CycleKernels.kernel r key).bind FairRecovery.reverse).bind _ =
      ((CycleKernels.kernel r key).bind FairRecovery.reverse).bind _
    apply bind_congr_of_support
    intro final supported
    simp only [Function.comp_def]
    rw [loop_ciphertext r message key final supported]
  simp_rw [each]
  rw [← PMF.map_bind,← PMF.bind_bind,CycleKernels.preserves,FairRecovery.reverse_preserve]

theorem loop_joint_state_law (r : Fin 95) (message : Bool) :
    ((tableEightBitLaw RecoveryRigidity.source message).bind (fun original =>
      evalConfigWithin (loopCode r) (Configuration.initial (NativeFiveStateSampler.rawInput original.1 original.2)) 663)).map
        NativePreparedState.state = (tableEightBitLaw RecoveryRigidity.source message).map (fun final => NativePreparedState.state
          (NativeCleanFiveStateSampler.finish
            ((NativeCleanFiveStateSampler.code (draw r)).length +
              (NativeContinuingFiveStateSampler.nextCode FairRecovery.sampleReverse).length + 2)
            final.1 final.2 {left := List.replicate 19 none} {left := [none]})) := by
  rw [PMF.map_bind]
  simp_rw [loop_initial_state_law]
  have h := congrArg (PMF.map (fun final : Fin 5 × Bool => NativePreparedState.state
    (NativeCleanFiveStateSampler.finish
      ((NativeCleanFiveStateSampler.code (draw r)).length +
        (NativeContinuingFiveStateSampler.nextCode FairRecovery.sampleReverse).length + 2)
      final.1 final.2 {left := List.replicate 19 none} {left := [none]}))) (loop_joint_preserves r message)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def] using h

def cleanBounded (r : Fin 95) : CryptoLogic.BoundedProgram := NativeCleanFiveStateSampler.bounded (draw r)
def loopBounded (r : Fin 95) : CryptoLogic.BoundedProgram :=
  NativeContinuingFiveStateSampler.bounded (draw r) FairRecovery.sampleReverse

theorem clean_polynomial_time (r : Fin 95) : PolynomialTime (cleanCode r) := (cleanBounded r).polynomialTime

theorem loop_polynomial_time (r : Fin 95) : PolynomialTime (loopCode r) := (loopBounded r).polynomialTime

end Machine.NativeCycleKernelSampler
