import Foundation.Crypto.Semantics.Machine.NativeCanonicalFairRecovery
import Foundation.Crypto.Logic.Polygraph.NativeReferenceFairRecovery
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation

/-! Actual native final-state and public-output equalities become exact game
steps. Retaining the original key as proof metadata still yields a positive
conditional recovery error, even after the charged packet-restoring caller.
The two programs have different time bounds; no timing equivalence is asserted. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
noncomputable section

def fullLaw (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin Machine.NativeCanonicalFairRecovery.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)) 1676).map Machine.NativePreparedState.state

def stationaryLaw (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin Machine.NativeCanonicalFairRecovery.stationaryCode
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)) 932).map Machine.NativePreparedState.state

def nativeGame (message : Bool) : Program Machine.NativePreparedState.State := .sample (fullLaw message)
def stationaryGame (message : Bool) : Program Machine.NativePreparedState.State := .sample (stationaryLaw message)

def fullReification (message : Bool) : ExactStep (nativeGame message) (stationaryGame message) :=
  .distribution (Machine.NativeCanonicalFairRecovery.full_cell_identity message)

def publicGame (message : Bool) : Program (Option (List Bool)) := .sample
  (Machine.evalWithin Machine.NativeCanonicalFairRecovery.code
    (Machine.NativePreparedKeyDecision.rawInput Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message) 1676)
def publicReferenceGame (message : Bool) : Program (Option (List Bool)) := .sample
  (Machine.evalWithin Machine.NativePreparedKeyDecision.code
    (Machine.NativePreparedKeyDecision.rawInput Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message) 930)

def publicReification (message : Bool) : ExactStep (publicGame message) (publicReferenceGame message) :=
  .distribution (Machine.NativeCanonicalFairRecovery.public_identity message)

theorem decode_finish (pc : Nat) (result : Fin 5 × Bool) :
    Machine.NativePreparedState.decode (Machine.NativePreparedState.state (Machine.NativePreparedState.finish pc result)) = result := by
  change (Machine.NativePreparedInternalResult.observe (Machine.NativePreparedState.finish pc result)).getD (0,false) = _
  rw [Machine.NativePreparedState.observe_finish]
  rfl

def cutJoint (v : OrderedGridVertex 32) (message : Bool) (beforePc afterPc : Nat) : PMF (Fin 5 × Fin 5) :=
  ((Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map Machine.NativePreparedState.state).bind
      (fun initial => ((Machine.NativeReferenceFairRecovery.kernelAt beforePc initial).bind
        (Machine.NativeCanonicalFairRecovery.callerKernelAt afterPc)).map
          (fun final => ((Machine.NativePreparedState.decode initial).1,(Machine.NativePreparedState.decode final).1)))

theorem cut_joint (v : OrderedGridVertex 32) (message : Bool) (beforePc afterPc : Nat) :
    cutJoint v message beforePc afterPc = (tableEightBitLaw v message).bind (fun original =>
      ((FairRecovery.forward original.1).bind FairRecovery.reverse).map (fun final => (original.1,final))) := by
  rw [cutJoint,Machine.NativePreparedState.initial_law,PMF.bind_map]
  apply congrArg (PMF.bind (tableEightBitLaw v message))
  funext original
  simp only [Function.comp_def,Machine.NativeReferenceFairRecovery.kernelAt_encode,Machine.NativePreparedState.decode_encode]
  rw [PMF.bind_map,PMF.map_bind]
  simp only [Function.comp_def,Machine.NativeCanonicalFairRecovery.callerKernelAt_clean,PMF.pure_map,decode_finish]
  rfl

theorem recovery_error (message : Bool) (beforePc afterPc : Nat) :
    (eventProb (cutJoint Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message beforePc afterPc)
      (fun pair => pair.1 ≠ pair.2)).toReal = 13037041 / 536870912 := by
  rw [cut_joint,Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  rw [event_bind_real]
  simp only [eventProb_map]
  have swap (x : Fin 5) : (fun y : Fin 5 => x ≠ y) = (fun y => y ≠ x) := funext (fun _ => propext ne_comm)
  simp_rw [swap]
  exact FairRecovery.recovery_error

theorem final_key_law (message : Bool) :
    (fullLaw message).map (fun final => (Machine.NativePreparedState.decode final).1) =
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source := by
  have h := congrArg (PMF.map (fun final => (Machine.NativePreparedState.decode final).1))
    (Machine.NativeCanonicalFairRecovery.transformed_law message)
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

theorem cut_final_is_actual_execution (message : Bool) (beforePc afterPc : Nat) :
    (cutJoint Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message beforePc afterPc).map Prod.snd =
      (fullLaw message).map (fun final => (Machine.NativePreparedState.decode final).1) := by
  rw [cut_joint,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  change (tableEightBitLaw Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message).bind
    (fun original => ((FairRecovery.forward original.1).bind FairRecovery.reverse).map id) = _
  simp only [PMF.map_id]
  rw [Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor,PMF.bind_map]
  simp only [Function.comp_def]
  rw [← PMF.bind_bind,FairRecovery.forward_preserve,FairRecovery.reverse_preserve]
  exact (final_key_law message).symm

end
end CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery
