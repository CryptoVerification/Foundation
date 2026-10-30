import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecoveryCipher
import Foundation.Crypto.Semantics.Machine.NativeReferenceFairRecovery
import Foundation.Crypto.Logic.Polygraph.NativeContinuingFairRecovery

/-! Connect the actual reference-cipher execution to the new fair roundtrip.
The recovery error retains the original key at the real 930-step cut as proof
metadata; the running machine does not receive a free copy of that key. -/
namespace CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open NativeContinuingFairRecovery (readState)
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem read_clean (pc : Nat) (result : Fin 5 × Bool) :
    readState (Machine.NativeReferenceFairRecovery.cleanEncode pc result) = result.1 :=
  NativeContinuingFairRecovery.read_finish pc result.1 result.2 _ _

def observedKernel (result : Fin 5 × Bool) : PMF (Fin 5) :=
  (Machine.evalConfigWithin Machine.NativeReferenceFairRecovery.continuation
    ((Machine.NativePreparedState.finish 0 result).resumeAt 0) 714).map NativeFairRecovery.observeKey

theorem observed_kernel_eq (result : Fin 5 × Bool) :
    observedKernel result = (FairRecovery.forward result.1).bind FairRecovery.reverse := by
  have h := congrArg (PMF.map readState) (Machine.NativeReferenceFairRecovery.continuation_run 0 0 result)
  simp only [PMF.map_comp,Function.comp_def,read_clean] at h
  exact h.trans (PMF.map_id _)

def cutJoint (v : OrderedGridVertex 32) (message : Bool) (pc : Nat) : PMF (Fin 5 × Fin 5) :=
  ((Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map Machine.NativePreparedState.state).bind
      (fun initial => (Machine.NativeReferenceFairRecovery.kernelAt pc initial).map
        (fun final => ((Machine.NativePreparedState.decode initial).1,readState final)))

theorem cut_joint (v : OrderedGridVertex 32) (message : Bool) (pc : Nat) :
    cutJoint v message pc = (tableEightBitLaw v message).bind (fun original =>
      ((FairRecovery.forward original.1).bind FairRecovery.reverse).map (fun final => (original.1,final))) := by
  rw [cutJoint,Machine.NativePreparedState.initial_law,PMF.bind_map]
  simp only [Function.comp_def,Machine.NativeReferenceFairRecovery.kernelAt_encode,
    PMF.map_comp,Machine.NativePreparedState.decode_encode,read_clean]

theorem recovery_error (message : Bool) (pc : Nat) :
    (eventProb (cutJoint Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message pc)
      (fun pair => pair.1 ≠ pair.2)).toReal = 13037041 / 536870912 := by
  rw [cut_joint,Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  rw [event_bind_real]
  simp only [eventProb_map]
  have swap (x : Fin 5) : (fun y : Fin 5 => x ≠ y) = (fun y => y ≠ x) :=
    funext (fun _ => propext ne_comm)
  simp_rw [swap]
  exact FairRecovery.recovery_error

theorem full_final_key_law (v : OrderedGridVertex 32) (message : Bool) :
    (Machine.evalConfigWithin Machine.NativeReferenceFairRecovery.code
      (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 1645).map NativeFairRecovery.observeKey =
      (tableEightBitLaw v message).bind (fun original => (FairRecovery.forward original.1).bind FairRecovery.reverse) := by
  have h := congrArg (PMF.map readState) (Machine.NativeReferenceFairRecovery.initial_law v message)
  rw [PMF.map_bind,PMF.bind_map] at h
  simp only [PMF.map_comp,Function.comp_def,Machine.NativeReferenceFairRecovery.kernelAt_encode,read_clean] at h
  change (Machine.evalConfigWithin Machine.NativeReferenceFairRecovery.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 1645).map NativeFairRecovery.observeKey =
    (tableEightBitLaw v message).bind (fun original => ((FairRecovery.forward original.1).bind FairRecovery.reverse).map id) at h
  simpa only [PMF.map_id] using h

theorem cut_final_is_actual_execution (v : OrderedGridVertex 32) (message : Bool) :
    (cutJoint v message (Machine.NativePreparedKeyDecision.code.length + Machine.NativeReferenceFairRecovery.continuation.length + 2)).map Prod.snd =
      (Machine.evalConfigWithin Machine.NativeReferenceFairRecovery.code
        (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 1645).map NativeFairRecovery.observeKey := by
  rw [cut_joint,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  change (tableEightBitLaw v message).bind (fun original => ((FairRecovery.forward original.1).bind FairRecovery.reverse).map id) = _
  simp only [PMF.map_id]
  exact (full_final_key_law v message).symm

theorem source_joint_law (message : Bool) :
    (Machine.evalConfigWithin Machine.NativeReferenceFairRecovery.code
      (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)) 1645).map Machine.NativePreparedState.state =
      (tableEightBitLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message).map
        (Machine.NativeReferenceFairRecovery.cleanEncode
          (Machine.NativePreparedKeyDecision.code.length + Machine.NativeReferenceFairRecovery.continuation.length + 2)) := by
  rw [Machine.NativeReferenceFairRecovery.initial_law,PMF.bind_map]
  simp only [Function.comp_def,Machine.NativeReferenceFairRecovery.kernelAt_encode]
  have h := congrArg (PMF.map (Machine.NativeReferenceFairRecovery.cleanEncode
    (Machine.NativePreparedKeyDecision.code.length + Machine.NativeReferenceFairRecovery.continuation.length + 2)))
      (FairRecoveryCipher.joint_roundtrip_preserve message)
  rw [PMF.map_bind] at h
  simpa only [PMF.map_comp,Function.comp_def] using h

end
end CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery
