import Foundation.Crypto.Logic.Polygraph.GeneralNativeRecovery

/-! Approximate cells and diagram edits whose endpoint outcomes are actual
native states. The event may be any predicate of the decoded key; kernels are
native continuations. Allocated path losses are equal conservative budgets. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells
open Foundation.Probability GeneralNativeRecovery
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

def targetLaw (message : Bool) (pc : Nat) : PMF State :=
  (tableEightBitLaw RecoveryRigidity.source message).map (fun result => Machine.NativePreparedState.state
    (Machine.NativePreparedState.finish pc result))

theorem target_actual (r : Fin 95) (message : Bool) :
    targetLaw message ((Machine.NativeReferenceCycleRecovery.code r).length + Machine.NativeKeyPairDecisionExecution.caller.length + 2) =
      NativeCanonicalCycleRecovery.fullLaw r message :=
  (Machine.NativeCanonicalCycleRecovery.transformed_law r message).symm

def sourceGame (message : Bool) (event : Fin 5 → Prop) : Observed where
  Outcome := State
  program := .sample (sourceLaw message)
  event s := event (Machine.NativePreparedState.decode s).1

def targetGame (message : Bool) (pc : Nat) (event : Fin 5 → Prop) : Observed where
  Outcome := State
  program := .sample (targetLaw message pc)
  event s := event (Machine.NativePreparedState.decode s).1

def budget (r : Fin 95) : ℝ≥0∞ := ENNReal.ofReal (13037041 / 536870912 + 1849 * (r.val : ℝ) / 524288)

theorem native_preserve (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    (sourceLaw message).bind (nativeKernel r beforePc afterPc) = targetLaw message afterPc := by
  rw [source_law,PMF.bind_map]
  simp only [Function.comp_def,native_encode]
  have h := congrArg (PMF.map (fun result : Fin 5 × Bool => Machine.NativePreparedState.state
    (Machine.NativePreparedState.finish afterPc result))) (Machine.NativeCycleKernelSampler.loop_joint_preserves r message)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def,targetLaw] using h

theorem stationary_preserve (message : Bool) (pc : Nat) :
    (sourceLaw message).bind (stationaryKernel pc) = targetLaw message pc := by
  rw [source_law,PMF.bind_map]
  simp only [Function.comp_def,stationary_encode]
  rfl

theorem decode_reset (pc : Nat) (s : State) : Machine.NativePreparedState.decode (reset pc s) = Machine.NativePreparedState.decode s := by
  induction s using Quotient.inductionOn with
  | h c => rfl

theorem cut_event (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    eventProb (GeneralKernelVariation.joint (sourceLaw message) (nativeKernel r beforePc afterPc))
      (fun pair => (Machine.NativePreparedState.decode pair.1).1 ≠ (Machine.NativePreparedState.decode pair.2).1) =
      eventProb (NativeCanonicalCycleRecovery.cutJoint r RecoveryRigidity.source message beforePc afterPc) (fun pair => pair.1 ≠ pair.2) := by
  have same : (GeneralKernelVariation.joint (sourceLaw message) (nativeKernel r beforePc afterPc)).map
      (fun pair => ((Machine.NativePreparedState.decode pair.1).1,(Machine.NativePreparedState.decode pair.2).1)) =
      NativeCanonicalCycleRecovery.cutJoint r RecoveryRigidity.source message beforePc afterPc := by
    rw [GeneralKernelVariation.joint,PMF.map_bind]
    simp only [PMF.map_comp,Function.comp_def]
    rfl
  rw [← same,eventProb_map]

theorem native_bad_bound (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    eventProb (GeneralKernelVariation.joint (sourceLaw message) (nativeKernel r beforePc afterPc))
      (fun pair => (Machine.NativePreparedState.decode pair.1).1 ≠ (Machine.NativePreparedState.decode pair.2).1) ≤ budget r := by
  rw [cut_event]
  have bound := ENNReal.ofReal_le_ofReal (NativeCanonicalCycleRecovery.recovery_error r message beforePc afterPc)
  rw [ENNReal.ofReal_toReal (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))] at bound
  exact bound

def nativeStep (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) :
    GameCoherence.Step (sourceGame message event) (targetGame message afterPc event) where
  kernel := nativeKernel r beforePc afterPc
  preserve := native_preserve r message beforePc afterPc
  bad pair := (Machine.NativePreparedState.decode pair.1).1 ≠ (Machine.NativePreparedState.decode pair.2).1
  agree x _ y _ good := by
    have same : (Machine.NativePreparedState.decode x).1 = (Machine.NativePreparedState.decode y).1 := not_ne_iff.mp good
    change event (Machine.NativePreparedState.decode x).1 ↔ event (Machine.NativePreparedState.decode y).1
    rw [same]
  loss := budget r
  bound := native_bad_bound r message beforePc afterPc

def stationaryStep (r : Fin 95) (message : Bool) (pc : Nat) (event : Fin 5 → Prop) :
    GameCoherence.Step (sourceGame message event) (targetGame message pc event) where
  kernel := stationaryKernel pc
  preserve := stationary_preserve message pc
  bad _ := False
  agree x _ y supported _ := by
    have same : y = reset pc x := by simpa [stationaryKernel] using supported
    subst y
    change event (Machine.NativePreparedState.decode x).1 ↔ event (Machine.NativePreparedState.decode (reset pc x)).1
    rw [decode_reset]
  loss := budget r
  bound := by simp [eventProb]

def recoveryCell (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) :
    GeneralApproximateGameCoherence.Cell4 (.step (nativeStep r message beforePc afterPc event))
      (.step (stationaryStep r message afterPc event)) (budget r) :=
  .generator ⟨discrepancy_bound r message beforePc afterPc,rfl⟩

def recoveryEdit (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) :
    GeneralApproximateDiagramEdits.Edit
      (GameCoherence.DiagramBridge.diagram (.step (nativeStep r message beforePc afterPc event)))
      (GameCoherence.DiagramBridge.diagram (.step (stationaryStep r message afterPc event))) (budget r) := by
  apply GeneralApproximateDiagramEdits.Edit.game
  simp only [GameCoherence.DiagramBridge.evaluate_diagram]
  exact recoveryCell r message beforePc afterPc event

def actualRecoveryCell (r : Fin 95) (message : Bool) (event : Fin 5 → Prop) :=
  recoveryCell r message (Machine.NativePreparedKeyDecision.code.length + (Machine.NativeReferenceCycleRecovery.continuation r).length + 2)
    ((Machine.NativeReferenceCycleRecovery.code r).length + Machine.NativeKeyPairDecisionExecution.caller.length + 2) event

def actualRecoveryEdit (r : Fin 95) (message : Bool) (event : Fin 5 → Prop) :=
  recoveryEdit r message (Machine.NativePreparedKeyDecision.code.length + (Machine.NativeReferenceCycleRecovery.continuation r).length + 2)
    ((Machine.NativeReferenceCycleRecovery.code r).length + Machine.NativeKeyPairDecisionExecution.caller.length + 2) event

theorem no_zero_cell (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) :
    ¬ Nonempty (GeneralApproximateGameCoherence.Cell4 (.step (nativeStep r message beforePc afterPc event))
      (.step (stationaryStep r message afterPc event)) 0) := by
  rintro ⟨cell⟩
  have upper := cell.sound.kernel_bound
  change GeneralKernelVariation.distance (sourceLaw message) (nativeKernel r beforePc afterPc) (stationaryKernel afterPc) ≤ 0 at upper
  have impossible := (discrepancy_lower r message beforePc afterPc).trans upper
  norm_num at impossible

end
end CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells
