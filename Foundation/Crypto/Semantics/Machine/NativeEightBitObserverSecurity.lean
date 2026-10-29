import Foundation.Crypto.Semantics.Machine.NativeCleanCipherContinuation
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitObserverBound

/-! Checked numeric bounds for the same continuing native execution.
The fixed caller and retained frames must be shared between the two games.
The key may be inspected; the statement is stronger than key-hidden observation
but concerns constrained adjacent implementations, not message secrecy. -/
namespace Machine.NativeEightBitObserverSecurity
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

theorem formatted_edge_bound (caller : Program) (T : ℕ) (hCaller : StopsEverywhere caller T)
    (u v : OrderedGridVertex 32) (he : faceEdge (orderedGridComplex 32) u v) (message : Bool)
    (inputSuffix outputSuffix : Tape) (observe : Configuration → Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code caller)
        (NativeControlledEightBitCipher.entry u message inputSuffix outputSuffix) (411 + T + 1)).map observe) (· = true))
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code caller)
        (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) (411 + T + 1)).map observe) (· = true)) ≤
        (37 / 128 : ℝ≥0∞) :=
  NativeCleanCipherContinuation.observer_bound caller T hCaller u v message inputSuffix outputSuffix
    (fun _ => True) _ (table_all_observers_edge_bound u v he message) observe trivial

theorem initial_edge_bound (caller : Program) (T : ℕ) (hCaller : StopsEverywhere caller T)
    (u v : OrderedGridVertex 32) (he : faceEdge (orderedGridComplex 32) u v) (message : Bool)
    (observe : Configuration → Bool)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    probabilityGap
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code caller)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request u message))) (411 + T + 1)).map observe) (· = true))
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code caller)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) (411 + T + 1)).map observe) (· = true)) ≤
        (37 / 128 : ℝ≥0∞) := by
  rw [NativeCleanCipherContinuation.initial_observation caller T hCaller observe hObserve u message,
    NativeCleanCipherContinuation.initial_observation caller T hCaller observe hObserve v message,
    PMF.map_bind, PMF.map_bind]
  exact table_probabilistic_event_edge_bound u v he message
    (fun result => (NativeCleanCipherContinuation.kernel caller T {} {} result).map observe) (· = true)

theorem toggle_initial_edge_bound (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool)
    (observe : Configuration → Bool)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    probabilityGap
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request u message))) 418).map observe) (· = true))
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map observe) (· = true)) ≤
        (37 / 128 : ℝ≥0∞) :=
  initial_edge_bound NativeCiphertextToggle.code 6 NativeCiphertextToggle.stops u v he message observe hObserve

end Machine.NativeEightBitObserverSecurity
