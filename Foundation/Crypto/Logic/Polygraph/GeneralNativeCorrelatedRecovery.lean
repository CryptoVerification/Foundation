import Foundation.Crypto.Logic.Polygraph.GeneralCorrelatedGameFrames
import Foundation.Crypto.Logic.Polygraph.GeneralNativeRecoveryCells

/-! Retain a possibly infinite register correlated through the ciphertext of
the actual native source. Local ciphertext preservation establishes both joint
laws. The register is semantic inherited state, not free native resampling. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery
open Foundation.Probability GeneralNativeRecovery GeneralNativeRecoveryCells CorrelatedGameFrames
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {C : Type}

def sourceFrame (message : Bool) (event : Fin 5 → Prop) (context : Bool → PMF C) : Frame (sourceGame message event) C :=
  GeneralCorrelatedGameFrames.stochasticTagged (sourceGame message event) (fun s => context (Machine.NativePreparedState.decode s).2)

def targetFrame (message : Bool) (pc : Nat) (event : Fin 5 → Prop) (context : Bool → PMF C) : Frame (targetGame message pc event) C :=
  GeneralCorrelatedGameFrames.stochasticTagged (targetGame message pc event) (fun s => context (Machine.NativePreparedState.decode s).2)

theorem native_ciphertext (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (x : State)
    (sourceSupported : x ∈ (sourceLaw message).support) (y : State) (targetSupported : y ∈ (nativeKernel r beforePc afterPc x).support) :
    (Machine.NativePreparedState.decode y).2 = (Machine.NativePreparedState.decode x).2 := by
  rw [source_law] at sourceSupported
  obtain ⟨original,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp sourceSupported
  rw [native_encode] at targetSupported
  obtain ⟨key,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp targetSupported
  rw [NativeCanonicalFairRecovery.decode_finish,Machine.NativePreparedState.decode_encode]

theorem native_compatible (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) (context : Bool → PMF C) :
    Compatible (sourceFrame message event context) (targetFrame message afterPc event context)
      (.step (nativeStep r message beforePc afterPc event)) := by
  apply GeneralCorrelatedGameFrames.compatible_stochasticTagged
  intro x sourceSupported y targetSupported
  rw [native_ciphertext r message beforePc afterPc x sourceSupported y targetSupported]

theorem stationary_compatible (r : Fin 95) (message : Bool) (pc : Nat) (event : Fin 5 → Prop) (context : Bool → PMF C) :
    Compatible (sourceFrame message event context) (targetFrame message pc event context)
      (.step (stationaryStep r message pc event)) := by
  apply GeneralCorrelatedGameFrames.compatible_stochasticTagged
  intro x _ y supported
  have same : y = reset pc x := by simpa [stationaryStep,stationaryKernel,GameCoherence.Path.kernel] using supported
  subst y
  change context (Machine.NativePreparedState.decode (reset pc x)).2 = context (Machine.NativePreparedState.decode x).2
  rw [decode_reset]

def framedCell (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop)
    (context : Bool → PMF C) (test : C → Prop) :=
  GeneralCorrelatedGameFrames.liftCell (sourceFrame message event context) (targetFrame message afterPc event context) test
    (recoveryCell r message beforePc afterPc event)
    (native_compatible r message beforePc afterPc event context) (stationary_compatible r message afterPc event context)

theorem framed_distance (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop)
    (context : Bool → PMF C) (test : C → Prop) :
    GeneralKernelVariation.distance ((sourceFrame message event context).observed test).program.eval
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (nativeStep r message beforePc afterPc event)) (native_compatible r message beforePc afterPc event context)).kernel
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (stationaryStep r message afterPc event)) (stationary_compatible r message afterPc event context)).kernel =
      GeneralKernelVariation.distance (sourceLaw message) (nativeKernel r beforePc afterPc) (stationaryKernel afterPc) :=
  GeneralCorrelatedGameFrames.lift_distance _ _ _ _ _ _ _

theorem framed_lower (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop)
    (context : Bool → PMF C) (test : C → Prop) :
    ENNReal.ofReal (3 / 256 : ℝ) ≤ GeneralKernelVariation.distance ((sourceFrame message event context).observed test).program.eval
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (nativeStep r message beforePc afterPc event)) (native_compatible r message beforePc afterPc event context)).kernel
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (stationaryStep r message afterPc event)) (stationary_compatible r message afterPc event context)).kernel := by
  rw [framed_distance]
  exact discrepancy_lower r message beforePc afterPc

def framedEdit (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop)
    (context : Bool → PMF C) (test : C → Prop) : GeneralApproximateDiagramEdits.Edit
      (GameCoherence.DiagramBridge.diagram (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (nativeStep r message beforePc afterPc event)) (native_compatible r message beforePc afterPc event context)))
      (GameCoherence.DiagramBridge.diagram (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (stationaryStep r message afterPc event)) (stationary_compatible r message afterPc event context))) (budget r) := by
  apply GeneralApproximateDiagramEdits.Edit.game
  simp only [GameCoherence.DiagramBridge.evaluate_diagram]
  exact framedCell r message beforePc afterPc event context test

end
end CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery
