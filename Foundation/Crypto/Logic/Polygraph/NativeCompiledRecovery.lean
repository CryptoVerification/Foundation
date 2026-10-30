import Foundation.Crypto.Semantics.Machine.NativeRecoveryIdentity
import Foundation.Crypto.Logic.Polygraph.NativeRecoverableCoupling
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation

/-! The kernels in this recovery cell are observations of the actual native
288-step forward and 101-step reverse. A separate 390-step continuing run
recovers each admitted full source state. Logical contextual whiskering
does not provide free native implementations of arbitrary contexts. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery
open Foundation.Probability Foundation.Logic.Polygraph GameCoherence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem decode_finish (pc : ℕ) (result : Fin 5 × Bool) :
    Machine.NativePreparedState.decode (Machine.NativePreparedState.state
      (Machine.NativePreparedState.finish pc result)) = result := by
  change (Machine.NativePreparedInternalResult.observe (Machine.NativePreparedState.finish pc result)).getD (0,false) = result
  rw [Machine.NativePreparedState.observe_finish]
  rfl

def nativeForward (message : Bool) (bit : Bool) : PMF (Fin 5) :=
  (Machine.NativeCompiledRecovery.forwardKernelAt 0 (NativeRecoverable.sourceView message bit)).map
    (fun state => (Machine.NativePreparedState.decode state).1)

theorem nativeForward_eq (message : Bool) : nativeForward message = Recoverable.forward := by
  funext bit
  unfold nativeForward NativeRecoverable.sourceView
  rw [Machine.NativeCompiledRecovery.forward_source, PMF.map_comp]
  have h : (fun state => (Machine.NativePreparedState.decode state).1) ∘
      (fun key => Machine.NativePreparedState.state (Machine.NativePreparedState.finish 0
        (Recoverable.targetResult message key))) = id := by
    funext key
    simp only [Function.comp_apply, decode_finish]
    rfl
  rw [h, PMF.map_id]

def nativeReverse (message : Bool) (key : Fin 5) : PMF Bool :=
  (Machine.NativeReverseCoupling.kernelAt 0 (NativeRecoverable.targetView message key)).map
    (fun state => Recoverable.parent (Machine.NativePreparedState.decode state).1)

theorem nativeReverse_eq (message : Bool) : nativeReverse message = (fun key => PMF.pure (Recoverable.parent key)) := by
  funext key
  unfold nativeReverse NativeRecoverable.targetView Machine.NativePreparedState.encode
  rw [Machine.NativeReverseCoupling.kernelAt_target, PMF.pure_map, decode_finish,
    NativeRecoverable.source_parent]

def forwardStep (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    Step (NativeRecoverable.sourceGame message event) (NativeRecoverable.targetGame message event) where
  kernel := nativeForward message
  preserve := by rw [nativeForward_eq]; rfl
  bad := Recoverable.bad
  agree bit admitted key supported good :=
    (NativeRecoverable.forwardStep message event).agree bit admitted key
      (by simpa only [nativeForward_eq, NativeRecoverable.forwardStep] using supported) good
  loss := 37 / 128
  bound := by
    rw [nativeForward_eq]
    exact (NativeRecoverable.forwardStep message event).bound

def reverseStep (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    Step (NativeRecoverable.targetGame message event) (NativeRecoverable.sourceGame message event) where
  kernel := nativeReverse message
  preserve := by
    rw [nativeReverse_eq]
    exact (NativeRecoverable.reverseStep message event).preserve
  bad := Recoverable.reverseBad
  agree key admitted bit supported good :=
    (NativeRecoverable.reverseStep message event).agree key admitted bit
      (by simpa only [nativeReverse_eq, NativeRecoverable.reverseStep] using supported) good
  loss := 37 / 128
  bound := by
    rw [nativeReverse_eq]
    exact (NativeRecoverable.reverseStep message event).bound

def roundtrip (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    Path (NativeRecoverable.sourceGame message event) (NativeRecoverable.sourceGame message event) :=
  .seq (.step (forwardStep message event)) (.step (reverseStep message event))

theorem roundtrip_kernel (message : Bool) (event : Machine.NativePreparedState.State → Prop) (bit : Bool) :
    (roundtrip message event).kernel bit = PMF.pure bit := by
  change (nativeForward message bit).bind (nativeReverse message) = _
  rw [nativeForward_eq, nativeReverse_eq]
  exact Recoverable.recovers bit

theorem roundtrip_loss (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    (roundtrip message event).loss = 37 / 64 := by
  change (37 / 128 : ℝ≥0∞) + 37 / 128 = 37 / 64
  exact NativeRecoverable.roundtrip_loss message event

def recoveryCell (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    Cell4 (roundtrip message event) (NativeRecoverable.stationary message event) :=
  .generator ⟨roundtrip_kernel message event,roundtrip_loss message event⟩

theorem path_matches_continuing_machine (pc : ℕ) (message : Bool)
    (event : Machine.NativePreparedState.State → Prop) (bit : Bool) :
    (Machine.NativeCompiledRecovery.roundtripKernelAt pc (NativeRecoverable.sourceView message bit)).map
      (fun state => Recoverable.parent (Machine.NativePreparedState.decode state).1) =
        (roundtrip message event).kernel bit := by
  unfold NativeRecoverable.sourceView
  rw [Machine.NativeCompiledRecovery.roundtrip_source, PMF.pure_map, decode_finish,
    NativeRecoverable.source_parent, roundtrip_kernel]

def recoveryEdit (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    DiagramBridge.Edit (DiagramBridge.diagram (roundtrip message event))
      (DiagramBridge.diagram (NativeRecoverable.stationary message event)) := .game (by
    rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram]
    exact recoveryCell message event)

def contextualRecovery {before after : Observed} (message : Bool)
    (event : Machine.NativePreparedState.State → Prop)
    (beforePath : Path before (NativeRecoverable.sourceGame message event))
    (afterPath : Path (NativeRecoverable.sourceGame message event) after) :
    Cell4 (.seq (.seq beforePath (roundtrip message event)) afterPath)
      (.seq (.seq beforePath (NativeRecoverable.stationary message event)) afterPath) :=
  .seq (.seq (.refl beforePath) (recoveryCell message event)) (.refl afterPath)

def executionGame (message : Bool) : Program Machine.NativePreparedState.State :=
  .sample ((Machine.evalConfigWithin Machine.NativeCompiledRecovery.bounded.program
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 0) message))
    (Machine.NativeCompiledRecovery.bounded.budget 39)).map Machine.NativePreparedState.state)

def stationaryExecutionGame (message : Bool) : Program Machine.NativePreparedState.State :=
  .sample ((Machine.evalConfigWithin Machine.NativeRecoveryIdentity.stationaryBounded.program
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 0) message))
    (Machine.NativeRecoveryIdentity.stationaryBounded.budget 39)).map Machine.NativePreparedState.state)

def executionReification (message : Bool) : ExactStep (executionGame message) (stationaryExecutionGame message) :=
  .distribution (Machine.NativeRecoveryIdentity.full_cell_identity message)

end
end CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery
