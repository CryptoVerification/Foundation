import Foundation.Crypto.Semantics.Machine.NativeEightBitSharpObservation
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitKeyTest

/-! A simple key-only witness for the native sharp gap. This isolates the
scope of the example: ciphertext is ignored, and private key labels are read. -/
namespace Machine.NativeEightBitKeyWitness
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

def resultTest : Option (Fin 5 × Bool) → Bool
  | none => false
  | some result => keyPairTest result

def observe (c : Configuration) : Bool := resultTest (NativeEightBitCipher.observe c)

theorem observe_equivalent (c d : Configuration) (h : c.Equivalent d) : observe c = observe d := by
  unfold observe
  rw [NativeControlledCipherInitial.observe_equivalent c d h]

theorem observed_run (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map observe =
        (tableEightBitLaw v message).map keyPairTest := by
  change ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
    (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map
    (resultTest ∘ NativeEightBitCipher.observe)) = _
  rw [← PMF.map_comp, NativeCleanCipherContinuation.toggle_initial_law, PMF.map_comp]
  have hfun : (resultTest ∘ (fun result : Fin 5 × Bool => some (result.1, !result.2))) = keyPairTest := by
    funext result
    rfl
  exact congrArg (fun f => (tableEightBitLaw v message).map f) hfun

theorem first_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 418).map observe)
      (· = true)).toReal = 1 := by
  rw [observed_run, keyPair_probability_first]

theorem second_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 418).map observe)
      (· = true)).toReal = 91 / 128 := by
  rw [observed_run, keyPair_probability_second]

theorem gap_attained (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 418).map observe) (· = true))
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 418).map observe) (· = true)) =
          (37 / 128 : ℝ≥0∞) := by
  rw [observed_run, observed_run, keyPair_gap]

end Machine.NativeEightBitKeyWitness
