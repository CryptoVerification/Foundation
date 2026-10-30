import Foundation.Crypto.Logic.Polygraph.GeneralApproximateDiagramEdits
import Foundation.Crypto.Logic.Polygraph.NativeCanonicalCycleRecovery

/-! Conditional discrepancy on the actual, infinite native-state type. The
source is the real 930-step execution; the kernels use the charged native
continuation and caller. A halt-padding comparator preserves the tape cells.
Retained-input observers can see both whole states, not just decoded keys. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev State := Machine.NativePreparedState.State

theorem state_infinite : Infinite State := by
  have injective : Function.Injective (fun pc : Nat => Machine.NativePreparedState.state
      (Machine.NativePreparedState.finish pc (0,false))) := by
    intro n m same
    exact ((Machine.NativePreparedState.state_eq_iff _ _).mp same).1
  exact Infinite.of_injective _ injective

noncomputable def sourceLaw (message : Bool) : PMF State :=
  (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 930).map
      Machine.NativePreparedState.state

theorem source_law (message : Bool) : sourceLaw message =
    (tableEightBitLaw RecoveryRigidity.source message).map Machine.NativePreparedState.encode :=
  Machine.NativePreparedState.initial_law RecoveryRigidity.source message

def nativeKernel (r : Fin 95) (beforePc afterPc : Nat) (initial : State) : PMF State :=
  (Machine.NativeReferenceCycleRecovery.kernelAt r beforePc initial).bind
    (Machine.NativeCanonicalFairRecovery.callerKernelAt afterPc)

def reset (pc : Nat) : State → State := Quotient.lift
  (Machine.NativeAdaptedRecoverableCoupling.atControl pc)
  (Machine.NativeAdaptedRecoverableCoupling.atControl_equivalent pc)

def stationaryKernel (pc : Nat) (initial : State) : PMF State := PMF.pure (reset pc initial)

theorem stationary_from_halt (r : Fin 95) (pc : Nat) (c : Machine.Configuration) :
    (Machine.evalConfigWithin (Machine.NativeCanonicalCycleRecovery.padding r) (c.resumeAt 0) 1).map
      (Machine.NativeAdaptedRecoverableCoupling.atControl pc) = stationaryKernel pc (Machine.NativePreparedState.state c) := by
  have run (n : Nat) (positive : 0 < n) :
      Machine.evalConfigWithin (List.replicate n .halt) (c.resumeAt 0) 1 = PMF.pure {c with pc := 0,halted := true} := by
    cases n with
    | zero => omega
    | succ n => simp [List.replicate_succ,Machine.evalConfigWithin,Machine.stepPMF,Machine.next,
      Machine.Configuration.resumeAt,Machine.Instruction.next]
  rw [Machine.NativeCanonicalCycleRecovery.padding,run _ (by omega),PMF.pure_map]
  rfl

theorem native_encode (r : Fin 95) (beforePc afterPc : Nat) (original : Fin 5 × Bool) :
    nativeKernel r beforePc afterPc (Machine.NativePreparedState.encode original) =
      ((CycleKernels.kernel r original.1).bind FairRecovery.reverse).map (fun key => Machine.NativePreparedState.state
        (Machine.NativePreparedState.finish afterPc (key,original.2))) := by
  rw [nativeKernel,Machine.NativeReferenceCycleRecovery.kernelAt_encode,PMF.bind_map]
  simp only [Function.comp_def,Machine.NativeCanonicalFairRecovery.callerKernelAt_clean]
  rfl

theorem stationary_encode (pc : Nat) (original : Fin 5 × Bool) :
    stationaryKernel pc (Machine.NativePreparedState.encode original) =
      PMF.pure (Machine.NativePreparedState.state (Machine.NativePreparedState.finish pc original)) := by rfl

theorem row_variation (r : Fin 95) (beforePc afterPc : Nat) (original : Fin 5 × Bool) :
    GeneralKernelVariation.variation (nativeKernel r beforePc afterPc (Machine.NativePreparedState.encode original))
      (stationaryKernel afterPc (Machine.NativePreparedState.encode original)) =
      GeneralKernelVariation.variation ((CycleKernels.kernel r original.1).bind FairRecovery.reverse) (PMF.pure original.1) := by
  rw [native_encode,stationary_encode]
  have h := GeneralKernelVariation.map_isometry
    ((CycleKernels.kernel r original.1).bind FairRecovery.reverse) (PMF.pure original.1)
    (fun key => Machine.NativePreparedState.state (Machine.NativePreparedState.finish afterPc (key,original.2)))
    (fun state => (Machine.NativePreparedState.decode state).1)
    (by
      intro key
      change (Machine.NativePreparedState.decode (Machine.NativePreparedState.state
        (Machine.NativePreparedState.finish afterPc (key,original.2)))).1 = key
      rw [NativeCanonicalFairRecovery.decode_finish])
  simpa only [PMF.pure_map] using h

theorem discrepancy (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    GeneralKernelVariation.distance (sourceLaw message) (nativeKernel r beforePc afterPc) (stationaryKernel afterPc) =
      ENNReal.ofReal (FiniteKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
        (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) PMF.pure) := by
  rw [source_law,GeneralKernelVariation.mapped_distance]
  simp_rw [row_variation]
  rw [RecoveryRigidity.joint_law_factor,GeneralKernelVariation.map_average]
  change GeneralKernelVariation.distance (RecoveryRigidity.keyLaw RecoveryRigidity.source)
    (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) PMF.pure = _
  exact GeneralKernelVariation.distance_finite_eq _ _ _

theorem discrepancy_bound (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    GeneralKernelVariation.distance (sourceLaw message) (nativeKernel r beforePc afterPc) (stationaryKernel afterPc) ≤
      ENNReal.ofReal (13037041 / 536870912 + 1849 * (r.val : ℝ) / 524288) := by
  rw [discrepancy]
  apply ENNReal.ofReal_le_ofReal
  have bound := NativeCycleKernels.loop_recovery_bound r false
  have same : NativeCycleKernels.loopKernel r false = (fun key => (CycleKernels.kernel r key).bind FairRecovery.reverse) :=
    funext (NativeCycleKernels.loop_kernel_eq r false)
  rw [same] at bound
  simpa only [FiniteKernelVariation.distance,FiniteKernelVariation.variation_pure,
    FiniteRecoveryError.failure,PMF.bind_pure,FiniteRecoveryError.different_probability] using bound

theorem discrepancy_lower (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) :
    ENNReal.ofReal (3 / 256 : ℝ) ≤ GeneralKernelVariation.distance (sourceLaw message)
      (nativeKernel r beforePc afterPc) (stationaryKernel afterPc) := by
  rw [discrepancy]
  apply ENNReal.ofReal_le_ofReal
  have bound := RecoveryError.recovery_error_lower (CycleKernels.kernel r) FairRecovery.reverse (CycleKernels.preserves r)
  simpa only [FiniteKernelVariation.distance,FiniteKernelVariation.variation_pure,
    FiniteRecoveryError.failure,FiniteRecoveryError.different_probability] using bound

theorem whole_state_observer_bound (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) {T : Type}
    (observer : State × State → PMF T) (event : T → Prop) :
    probabilityGap
      (eventProb ((GeneralKernelVariation.joint (sourceLaw message) (nativeKernel r beforePc afterPc)).bind observer) event)
      (eventProb ((GeneralKernelVariation.joint (sourceLaw message) (stationaryKernel afterPc)).bind observer) event) ≤
      ENNReal.ofReal (13037041 / 536870912 + 1849 * (r.val : ℝ) / 524288) :=
  (GeneralKernelVariation.joint_observer_bound _ _ _ observer event).trans (discrepancy_bound r message beforePc afterPc)

end
end CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery
