import Foundation.Crypto.Semantics.Machine.NativeKeyPairObserver

/-! Native key-label testing is part of the same continuing execution as
cipher generation, physical history erasure and ciphertext toggling.
The final observation only reads the decision bit written by native code. -/
namespace Machine.NativeKeyPairDecisionExecution
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

def caller : Program := NativeCiphertextToggle.code.followedBy NativeKeyPairObserver.code

def code : Program := NativeCleanCipherContinuation.code caller

def readDecision (c : Configuration) : Option Bool := c.outputTape.left.getD 0 none

theorem readDecision_equivalent (c d : Configuration) (h : c.Equivalent d) :
    readDecision c = readDecision d := h.2.2.2.2.1 0

theorem caller_stops : StopsEverywhere caller 30 :=
  NativeUniformSequence.stops _ _ 6 23 NativeCiphertextToggle.stops NativeKeyPairObserver.stops

theorem stops : StopsEverywhere code 442 :=
  NativeCleanCipherContinuation.stops caller 30 caller_stops

theorem caller_decision (result : Fin 5 × Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin caller
      ((NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).resumeAt 0) 30).map
      readDecision = PMF.pure (some (keyPairTest result)) := by
  unfold caller
  change (evalConfigWithin (NativeCiphertextToggle.code.followedBy NativeKeyPairObserver.code)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1)
        {inputSuffix with left := List.replicate 27 none ++ inputSuffix.left})
      {outputSuffix with left := some result.2 :: outputSuffix.left}) (6 + 23 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 6 23 NativeCiphertextToggle.stops NativeKeyPairObserver.stops,
    NativeCiphertextToggle.run, PMF.pure_bind]
  change ((evalConfigWithin NativeKeyPairObserver.code
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1)
        {inputSuffix with left := List.replicate 27 none ++ inputSuffix.left})
      {outputSuffix with left := some (!result.2) :: outputSuffix.left}) 23).map _).map _ = _
  rw [NativeKeyPairObserver.run, PMF.pure_map, PMF.pure_map]
  rw [NativeKeyPairObserver.accepts_encoded result.1 result.2]
  cases outputSuffix.right <;> simp [readDecision, Tape.moveRight, Tape.write]

theorem kernel_decision (result : Fin 5 × Bool) (inputSuffix outputSuffix : Tape) :
    (NativeCleanCipherContinuation.kernel caller 30 inputSuffix outputSuffix result).map readDecision =
      PMF.pure (some (keyPairTest result)) := by
  unfold NativeCleanCipherContinuation.kernel
  rw [PMF.map_comp]
  change (evalConfigWithin caller
    ((NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).resumeAt 0) 30).map readDecision = _
  exact caller_decision result inputSuffix outputSuffix

theorem formatted_law (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 442).map
      readDecision = (tableEightBitLaw v message).map (fun result => some (keyPairTest result)) := by
  unfold code
  rw [NativeCleanCipherContinuation.run caller 30 caller_stops, PMF.map_bind]
  simp only [kernel_decision]
  rfl

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 442).map readDecision =
        (tableEightBitLaw v message).map (fun result => some (keyPairTest result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeControlledCipherInitial.entry_equivalent v message).symm 442 _ readDecision_equivalent]
  exact formatted_law v message {} {}

theorem haltsWithin (input : List Bool) : HaltsWithin code input 442 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 442
  polynomial := PolynomiallyBounded.const 442
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem acceptance_law (v : OrderedGridVertex 32) (message : Bool) :
    eventProb ((evalConfigWithin code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 442).map readDecision)
      (· = some true) = eventProb ((tableEightBitLaw v message).map keyPairTest) (· = true) := by
  rw [initial_law, eventProb_map, eventProb_map]
  simp only [Option.some.injEq]

theorem edge_bound (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin code
        (Configuration.initial (List.ofFn (EightBitCipherControl.request u message))) 442).map readDecision) (· = some true))
      (eventProb ((evalConfigWithin code
        (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 442).map readDecision) (· = some true)) ≤
        (37 / 128 : ℝ≥0∞) := by
  rw [acceptance_law, acceptance_law]
  have h := table_all_observers_edge_bound u v he message
    (fun result => PMF.pure (keyPairTest result)) trivial
  simpa only [observerGap, PMF.map, Function.comp_def] using h

theorem first_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 442).map readDecision)
      (· = some true)).toReal = 1 := by
  rw [initial_law, eventProb_map]
  simpa only [eventProb_map, Option.some.injEq] using keyPair_probability_first message

theorem second_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 442).map readDecision)
      (· = some true)).toReal = 91 / 128 := by
  rw [initial_law, eventProb_map]
  simpa only [eventProb_map, Option.some.injEq] using keyPair_probability_second message

theorem gap_attained (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin code
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 0) message))) 442).map readDecision)
        (· = some true))
      (eventProb ((evalConfigWithin code
        (Configuration.initial (List.ofFn (EightBitCipherControl.request (sharpTableChain 2) message))) 442).map readDecision)
        (· = some true)) = (37 / 128 : ℝ≥0∞) := by
  rw [initial_law, initial_law, eventProb_map, eventProb_map]
  simpa only [eventProb_map, Option.some.injEq] using keyPair_gap message

end Machine.NativeKeyPairDecisionExecution
