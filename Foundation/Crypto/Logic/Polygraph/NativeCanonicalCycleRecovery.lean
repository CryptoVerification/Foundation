import Foundation.Crypto.Semantics.Machine.NativeCanonicalCycleRecovery
import Foundation.Crypto.Logic.Polygraph.NativeCycleKernels
import Foundation.Crypto.Logic.Polygraph.NativeCanonicalFairRecovery
import Foundation.Crypto.Logic.Polygraph.NativeReferenceFairRecovery
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation

/-! Reify end-to-end native equality for every local kernel edit. The cut
joint retains the original key only as proof metadata and has the actual final
key marginal. Positive conditional recovery error is bounded separately. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCanonicalCycleRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
open NativeCanonicalFairRecovery (decode_finish)
noncomputable section

def fullLaw (r : Fin 95) (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin (Machine.NativeCanonicalCycleRecovery.code r)
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)) 1676).map Machine.NativePreparedState.state

def stationaryLaw (r : Fin 95) (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin (Machine.NativeCanonicalCycleRecovery.stationaryCode r)
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)) 932).map Machine.NativePreparedState.state

def nativeGame (r : Fin 95) (message : Bool) : Program Machine.NativePreparedState.State := .sample ((fullLaw r) message)
def stationaryGame (r : Fin 95) (message : Bool) : Program Machine.NativePreparedState.State := .sample ((stationaryLaw r) message)

def fullReification (r : Fin 95) (message : Bool) : ExactStep ((nativeGame r) message) ((stationaryGame r) message) :=
  .distribution ((Machine.NativeCanonicalCycleRecovery.full_cell_identity r) message)

def publicGame (r : Fin 95) (message : Bool) : Program (Option (List Bool)) := .sample
  (Machine.evalWithin (Machine.NativeCanonicalCycleRecovery.code r)
    (Machine.NativePreparedKeyDecision.rawInput Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message) 1676)
def publicReferenceGame (message : Bool) : Program (Option (List Bool)) := .sample
  (Machine.evalWithin Machine.NativePreparedKeyDecision.code
    (Machine.NativePreparedKeyDecision.rawInput Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message) 930)

def publicReification (r : Fin 95) (message : Bool) : ExactStep ((publicGame r) message) (publicReferenceGame message) :=
  .distribution ((Machine.NativeCanonicalCycleRecovery.public_identity r) message)

def cutJoint (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) (beforePc afterPc : Nat) : PMF (Fin 5 × Fin 5) :=
  ((Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map Machine.NativePreparedState.state).bind
      (fun initial => (((Machine.NativeReferenceCycleRecovery.kernelAt r) beforePc initial).bind
        (Machine.NativeCanonicalFairRecovery.callerKernelAt afterPc)).map
          (fun final => ((Machine.NativePreparedState.decode initial).1,(Machine.NativePreparedState.decode final).1)))

theorem cut_joint (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) (beforePc afterPc : Nat) :
    (cutJoint r) v message beforePc afterPc = (tableEightBitLaw v message).bind (fun original =>
      (((CycleKernels.kernel r) original.1).bind FairRecovery.reverse).map (fun final => (original.1,final))) := by
  rw [cutJoint,Machine.NativePreparedState.initial_law,PMF.bind_map]
  apply congrArg (PMF.bind (tableEightBitLaw v message))
  funext original
  simp only [Function.comp_def,(Machine.NativeReferenceCycleRecovery.kernelAt_encode r),Machine.NativePreparedState.decode_encode]
  rw [PMF.bind_map,PMF.map_bind]
  simp only [Function.comp_def,Machine.NativeCanonicalFairRecovery.callerKernelAt_clean,PMF.pure_map,decode_finish]
  rfl

theorem recovery_error (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    (eventProb ((cutJoint r) Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message beforePc afterPc)
      (fun pair => pair.1 ≠ pair.2)).toReal ≤ 13037041 / 536870912 + 1849 * (r.val : ℝ) / 524288 := by
  rw [(cut_joint r),Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  rw [event_bind_real]
  simp only [eventProb_map]
  have swap (x : Fin 5) : (fun y : Fin 5 => x ≠ y) = (fun y => y ≠ x) := funext (fun _ => propext ne_comm)
  simp_rw [swap]
  have bound := NativeCycleKernels.loop_recovery_bound r false
  have same : NativeCycleKernels.loopKernel r false =
      (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) := funext (NativeCycleKernels.loop_kernel_eq r false)
  rw [same] at bound
  simpa only [FiniteRecoveryError.failure,PMF.bind_pure] using bound

theorem final_key_law (r : Fin 95) (message : Bool) :
    ((fullLaw r) message).map (fun final => (Machine.NativePreparedState.decode final).1) =
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source := by
  have h := congrArg (PMF.map (fun final => (Machine.NativePreparedState.decode final).1))
    ((Machine.NativeCanonicalCycleRecovery.transformed_law r) message)
  have right (pc : Nat) :
      ((tableEightBitLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message).map
        (fun result => Machine.NativePreparedState.state (Machine.NativePreparedState.finish pc result))).map
          (fun final => (Machine.NativePreparedState.decode final).1) =
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
          Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source := by
    rw [PMF.map_comp]
    simp only [Function.comp_def,decode_finish]
    rw [Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.map_comp]
    change (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source).map id = _
    exact PMF.map_id _
  exact h.trans (right _)

theorem cut_final_is_actual_execution (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    ((cutJoint r) Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message beforePc afterPc).map Prod.snd =
      ((fullLaw r) message).map (fun final => (Machine.NativePreparedState.decode final).1) := by
  rw [(cut_joint r),PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  change (tableEightBitLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message).bind
    (fun original => (((CycleKernels.kernel r) original.1).bind FairRecovery.reverse).map id) = _
  simp only [PMF.map_id]
  rw [Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  rw [← PMF.bind_bind,(CycleKernels.preserves r),FairRecovery.reverse_preserve]
  exact ((final_key_law r) message).symm

end
end CryptoLogic.Polygraph.Experiment.NativeCanonicalCycleRecovery
