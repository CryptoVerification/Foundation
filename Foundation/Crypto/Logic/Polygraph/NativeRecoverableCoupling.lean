import Foundation.Crypto.Logic.Polygraph.NativeStateCoherence
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoverableCoupling

/-! Alternative couplings of the same native endpoint laws, represented on
finite indices of their reachable complete cell states. The repaired forward
has a deterministic left inverse and the same 37/128 local loss. This is not
an identity on arbitrary unreachable configurations or a compiled sampler. -/
namespace CryptoLogic.Polygraph.Experiment.NativeRecoverable
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Machine.NativePreparedState (State encode)
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

def sourceView (message bit : Bool) : State := encode (Recoverable.sourceResult message bit)
def targetView (message : Bool) (key : Fin 5) : State := encode (Recoverable.targetResult message key)

theorem source_native_law (message : Bool) :
    Recoverable.sourceLaw.map (sourceView message) = NativeState.nativeLaw (sharpTableChain 0) message := by
  have h := congrArg (fun law : PMF (Fin 5 × Bool) => law.map encode) (Recoverable.source_law message)
  rw [PMF.map_comp] at h
  rw [NativeState.nativeLaw_eq]
  exact h

theorem target_native_law (message : Bool) :
    Recoverable.targetLaw.map (targetView message) = NativeState.nativeLaw (sharpTableChain 2) message := by
  have h := congrArg (fun law : PMF (Fin 5 × Bool) => law.map encode) (Recoverable.target_law message)
  rw [PMF.map_comp] at h
  rw [NativeState.nativeLaw_eq]
  exact h

theorem source_parent (message bit : Bool) : Recoverable.parent (Recoverable.sourceResult message bit).1 = bit := by
  cases bit <;> rfl

theorem sourceView_injective (message : Bool) : Function.Injective (sourceView message) := by
  intro a b same
  have h := congrArg (fun state => Recoverable.parent (Machine.NativePreparedState.decode state).1) same
  simpa only [sourceView, Machine.NativePreparedState.decode_encode, source_parent] using h

theorem targetView_injective (message : Bool) : Function.Injective (targetView message) := by
  intro a b same
  have h := Machine.NativePreparedState.encode_injective same
  exact congrArg Prod.fst h

def stateForward (message : Bool) (s : State) : PMF State :=
  (Recoverable.forward (Recoverable.parent (Machine.NativePreparedState.decode s).1)).map (targetView message)

def stateReverse (message : Bool) (s : State) : PMF State :=
  PMF.pure (sourceView message (Recoverable.parent (Machine.NativePreparedState.decode s).1))

theorem state_roundtrip (message bit : Bool) :
    (stateForward message (sourceView message bit)).bind (stateReverse message) = PMF.pure (sourceView message bit) := by
  simp only [stateForward, sourceView, Machine.NativePreparedState.decode_encode, source_parent, PMF.bind_map,
    Function.comp_def, stateReverse, targetView, Recoverable.targetResult]
  have h := congrArg (fun law : PMF Bool => law.map (sourceView message)) (Recoverable.recovers bit)
  rw [PMF.map_comp, PMF.pure_map] at h
  exact h

theorem state_forward_preserves (message : Bool) :
    (NativeState.nativeLaw (sharpTableChain 0) message).bind (stateForward message) =
      NativeState.nativeLaw (sharpTableChain 2) message := by
  rw [← source_native_law, ← target_native_law, PMF.bind_map]
  simp only [stateForward, sourceView, Machine.NativePreparedState.decode_encode, source_parent, Function.comp_def]
  rw [← PMF.map_bind]
  rfl

theorem state_reverse_preserves (message : Bool) :
    (NativeState.nativeLaw (sharpTableChain 2) message).bind (stateReverse message) =
      NativeState.nativeLaw (sharpTableChain 0) message := by
  rw [← source_native_law, ← target_native_law, PMF.bind_map]
  simp only [stateReverse, targetView, Recoverable.targetResult, Machine.NativePreparedState.decode_encode, Function.comp_def]
  have h := congrArg (fun law : PMF Bool => law.map (sourceView message)) Recoverable.reverse_preserves
  rw [PMF.map_comp] at h
  exact h

theorem supported_state_recovers (message : Bool) (s : State)
    (supported : s ∈ (NativeState.nativeLaw (sharpTableChain 0) message).support) :
    (stateForward message s).bind (stateReverse message) = PMF.pure s := by
  rw [← source_native_law, PMF.mem_support_map_iff] at supported
  obtain ⟨bit, _, rfl⟩ := supported
  exact state_roundtrip message bit

def sourceGame (message : Bool) (event : State → Prop) : Observed :=
  ⟨Bool, .sample Recoverable.sourceLaw, fun bit => event (sourceView message bit)⟩

def targetGame (message : Bool) (event : State → Prop) : Observed :=
  ⟨Fin 5, .sample Recoverable.targetLaw, fun key => event (targetView message key)⟩

def forwardStep (message : Bool) (event : State → Prop) : Step (sourceGame message event) (targetGame message event) where
  kernel := Recoverable.forward
  preserve := rfl
  bad := Recoverable.bad
  agree bit _ key _ good := by
    have same : key = (Recoverable.sourceResult message bit).1 := by
      cases bit <;> exact not_ne_iff.mp good
    have h := Recoverable.result_agrees message bit key same
    change event (encode (Recoverable.sourceResult message bit)) ↔ event (encode (Recoverable.targetResult message key))
    rw [h]
  loss := 37 / 128
  bound := by
    change eventProb Recoverable.joint Recoverable.bad ≤ _
    rw [Recoverable.bad_probability]

def reverseStep (message : Bool) (event : State → Prop) : Step (targetGame message event) (sourceGame message event) where
  kernel key := PMF.pure (Recoverable.parent key)
  preserve := Recoverable.reverse_preserves
  bad := Recoverable.reverseBad
  agree key _ bit _ good := by
    have same : key = (Recoverable.sourceResult message bit).1 := by
      cases bit <;> exact not_ne_iff.mp good
    have h := Recoverable.result_agrees message bit key same
    change event (encode (Recoverable.targetResult message key)) ↔ event (encode (Recoverable.sourceResult message bit))
    rw [h]
  loss := 37 / 128
  bound := by
    change eventProb (Recoverable.targetLaw.bind fun key =>
      (PMF.pure (Recoverable.parent key)).map fun bit => (key,bit)) Recoverable.reverseBad ≤ _
    simp only [PMF.pure_map]
    change eventProb Recoverable.reverseJoint Recoverable.reverseBad ≤ _
    rw [Recoverable.reverse_bad_probability]

def roundtrip (message : Bool) (event : State → Prop) : Path (sourceGame message event) (sourceGame message event) :=
  .seq (.step (forwardStep message event)) (.step (reverseStep message event))

theorem roundtrip_kernel (message : Bool) (event : State → Prop) (bit : Bool) :
    (roundtrip message event).kernel bit = PMF.pure bit := Recoverable.recovers bit

theorem roundtrip_loss (message : Bool) (event : State → Prop) : (roundtrip message event).loss = 37 / 64 := by
  change (37 / 128 : ℝ≥0∞) + 37 / 128 = 37 / 64
  rw [ENNReal.div_add_div_same, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

def stationaryStep (message : Bool) (event : State → Prop) : Step (sourceGame message event) (sourceGame message event) :=
  { Step.ofMap _ _ id (PMF.map_id _) (fun _ _ => Iff.rfl) with
    loss := 37 / 64
    bound := by
      change eventProb _ (fun _ => False) ≤ _
      simp [eventProb] }

def stationary (message : Bool) (event : State → Prop) : Path (sourceGame message event) (sourceGame message event) :=
  .step (stationaryStep message event)

def recoveryCell (message : Bool) (event : State → Prop) :
    Cell4 (roundtrip message event) (stationary message event) :=
  .generator ⟨roundtrip_kernel message event, roundtrip_loss message event⟩

def recoveryEdit (message : Bool) (event : State → Prop) :
    DiagramBridge.Edit (DiagramBridge.diagram (roundtrip message event))
      (DiagramBridge.diagram (stationary message event)) := .game (by
    rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram]
    exact recoveryCell message event)

def contextualRecovery {before after : Observed} (message : Bool) (event : State → Prop)
    (beforePath : Path before (sourceGame message event)) (afterPath : Path (sourceGame message event) after) :
    Cell4 (.seq (.seq beforePath (roundtrip message event)) afterPath)
      (.seq (.seq beforePath (stationary message event)) afterPath) :=
  .seq (.seq (.refl beforePath) (recoveryCell message event)) (.refl afterPath)

end
end CryptoLogic.Polygraph.Experiment.NativeRecoverable
