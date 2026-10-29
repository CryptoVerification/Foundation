import Foundation.Crypto.Logic.Polygraph.NativeStateTransition

/-! Full cell-state/native and finite-result routes have the same conditional
kernel on every input state, including states outside the execution support. -/
namespace CryptoLogic.Polygraph.Experiment.NativeState
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Machine.NativePreparedState (State Result encode decode decode_encode)
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

def referenceGame (v : Vertex) (message : Bool) (event : State → Prop) : Observed :=
  FiniteMaximal.game (tableEightBitLaw v message) (fun x => event (encode x))

def toFinite (v : Vertex) (message : Bool) (event : State → Prop) :
    Step (game v message event) (referenceGame v message event) :=
  Step.ofMap _ _ decode (by
    change (nativeLaw v message).map decode = tableEightBitLaw v message
    rw [nativeLaw_eq, PMF.map_comp]
    have h : decode ∘ encode = id := funext decode_encode
    rw [h, PMF.map_id]) (by
      intro s supported
      change s ∈ (nativeLaw v message).support at supported
      rw [nativeLaw_eq, PMF.mem_support_map_iff] at supported
      obtain ⟨x, _, rfl⟩ := supported
      change event (encode x) ↔ event (encode (decode (encode x)))
      rw [decode_encode])

def fromFinite (v : Vertex) (message : Bool) (event : State → Prop) :
    Step (referenceGame v message event) (game v message event) :=
  Step.ofMap _ _ encode (by
    change (tableEightBitLaw v message).map encode = nativeLaw v message
    rw [nativeLaw_eq]) (fun _ _ => Iff.rfl)

def direct (u v : Vertex) (message : Bool) (event : State → Prop) :
    Path (game u message event) (game v message event) := .step (transition u v message event)

def factored (u v : Vertex) (message : Bool) (event : State → Prop) :
    Path (game u message event) (game v message event) :=
  .seq (.step (toFinite u message event))
    (.seq (.step (FiniteMaximal.step (tableEightBitLaw u message) (tableEightBitLaw v message)
      (fun x => event (encode x)))) (.step (fromFinite v message event)))

theorem factorization_kernel (u v : Vertex) (message : Bool) (event : State → Prop) (s : State) :
    (direct u v message event).kernel s = (factored u v message event).kernel s := by
  simp only [direct, factored, Path.kernel, transition, toFinite, fromFinite, Step.ofMap,
    PMF.pure_bind, FiniteMaximal.step, EncodedMaximal.kernel]
  rfl

theorem factorization_loss (u v : Vertex) (message : Bool) (event : State → Prop) :
    (direct u v message event).loss = (factored u v message event).loss := by
  change ENNReal.ofReal (finiteVariation (tableEightBitLaw u message) (tableEightBitLaw v message)) =
    0 + (ENNReal.ofReal (finiteVariation (tableEightBitLaw u message) (tableEightBitLaw v message)) + 0)
  simp

def factorizationCell (u v : Vertex) (message : Bool) (event : State → Prop) :
    Cell4 (direct u v message event) (factored u v message event) :=
  .generator ⟨factorization_kernel u v message event, factorization_loss u v message event⟩

def factorizationEdit (u v : Vertex) (message : Bool) (event : State → Prop) :
    DiagramBridge.Edit (DiagramBridge.diagram (direct u v message event))
      (DiagramBridge.diagram (factored u v message event)) := .game (by
    rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram]
    exact factorizationCell u v message event)

def contextualFactorization {before after : Observed} (u v : Vertex) (message : Bool)
    (event : State → Prop) (beforePath : Path before (game u message event))
    (afterPath : Path (game v message event) after) :
    Cell4 (.seq (.seq beforePath (direct u v message event)) afterPath)
      (.seq (.seq beforePath (factored u v message event)) afterPath) :=
  .seq (.seq (.refl beforePath) (factorizationCell u v message event)) (.refl afterPath)


theorem supported_exit (v : Vertex) (message : Bool) (c : Machine.Configuration)
    (supported : c ∈ (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
      (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).support) :
    ∃ result ∈ (tableEightBitLaw v message).support,
      c.Equivalent (Machine.NativePreparedState.finish (Machine.NativePreparedKeyDecision.preparation.length + Machine.NativePreparedKeyDecision.source.length + 2) result) := by
  have hs : Machine.NativePreparedState.state c ∈ (nativeLaw v message).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨c, supported, rfl⟩
  rw [nativeLaw_eq, PMF.mem_support_map_iff] at hs
  obtain ⟨result, hr, same⟩ := hs
  exact ⟨result, hr, (Machine.NativePreparedState.state_eq_iff _ _).mp same.symm⟩

def liftEvent (event : Machine.Configuration → Prop)
    (invariant : ∀ c d, c.Equivalent d → (event c ↔ event d)) : State → Prop :=
  Quotient.lift event (fun c d h => propext (invariant c d h))

theorem full_state_event_bound (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : Machine.Configuration → Prop)
    (invariant : ∀ c d, c.Equivalent d → (event c ↔ event d)) :
    probabilityGap
      (eventProb (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
        (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput u message)) 930) event)
      (eventProb (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
        (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930) event) ≤
      (37 / 128 : ℝ≥0∞) := by
  have h := edge_sound u v edge message (liftEvent event invariant)
  unfold nativeLaw at h
  rw [eventProb_map, eventProb_map] at h
  exact h

end
end CryptoLogic.Polygraph.Experiment.NativeState
