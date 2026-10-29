import Foundation.Crypto.Semantics.Machine.NativeEightBitObserverSecurity
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitCountTest

/-! An exact-count Boolean observation attains 37/128 after the actual ciphertext
caller. This observes the retained secret key, and is not message advantage.
The predicate is computable using integers; a native runtime for evaluating
this observation is not charged or asserted here. -/
namespace Machine.NativeEightBitSharpObservation
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

def resultTest (message : Bool) : Option (Fin 5 × Bool) → Bool
  | none => false
  | some result => tableCountTest (sharpTableChain 0) (sharpTableChain 2) message (result.1, !result.2)

def observe (message : Bool) (c : Configuration) : Bool :=
  resultTest message (NativeEightBitCipher.observe c)

theorem observe_equivalent (message : Bool) (c d : Configuration) (h : c.Equivalent d) :
    observe message c = observe message d := by
  unfold observe
  rw [NativeControlledCipherInitial.observe_equivalent c d h]

theorem observed_run (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map
      (observe message) = (tableEightBitLaw v message).map
        (positiveTest (tableEightBitLaw (sharpTableChain 0) message)
          (tableEightBitLaw (sharpTableChain 2) message)) := by
  change ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
    (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map
    (resultTest message ∘ NativeEightBitCipher.observe)) = _
  rw [← PMF.map_comp, NativeCleanCipherContinuation.toggle_initial_law, PMF.map_comp]
  simp only [Function.comp_def]
  have hfun : (fun result : Fin 5 × Bool => resultTest message (some (result.1, !result.2))) =
      positiveTest (tableEightBitLaw (sharpTableChain 0) message)
        (tableEightBitLaw (sharpTableChain 2) message) := by
    funext result
    change tableCountTest (sharpTableChain 0) (sharpTableChain 2) message
      (result.1, !(!result.2)) = _
    simp only [Bool.not_not, Prod.mk.eta]
    exact congrFun (positiveTest_eq_countTest (sharpTableChain 0) (sharpTableChain 2) message).symm result
  exact congrArg (fun f => (tableEightBitLaw v message).map f) hfun

theorem gap_attained (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 418).map
        (observe message)) (· = true))
      (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 418).map
        (observe message)) (· = true)) = (37 / 128 : ℝ≥0∞) := by
  rw [observed_run, observed_run, positiveTest_attains, table_finiteVariation_eq,
    tableEightBitJointDistance_eq_jointTV, sharpTableChain_jointTV,
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem actual_edge_and_gap (message : Bool) :
    faceEdge (orderedGridComplex 32) (sharpTableChain 0) (sharpTableChain 2) ∧
      probabilityGap
        (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
          (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 418).map
          (observe message)) (· = true))
        (eventProb ((evalConfigWithin (NativeCleanCipherContinuation.code NativeCiphertextToggle.code)
          (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 418).map
          (observe message)) (· = true)) = (37 / 128 : ℝ≥0∞) :=
  ⟨sharpTableChain_edge, gap_attained message⟩

end Machine.NativeEightBitSharpObservation
