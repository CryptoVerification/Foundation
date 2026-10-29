import Foundation.Crypto.Semantics.Machine.NativePreparedKeyDecision

/-! Recover the retained labelled key/ciphertext pair from the actual final
configuration. This is an internal-state observation, not a public output
or a further native adversary instruction. The native program is unchanged. -/
namespace Machine.NativePreparedInternalResult
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

def undoToggle (result : Fin 5 × Bool) : Fin 5 × Bool := (result.1, !result.2)

def withoutDecision (c : Configuration) : Configuration :=
  {c with outputTape := {c.outputTape with left := c.outputTape.left.drop 1}}

def observe (c : Configuration) : Option (Fin 5 × Bool) :=
  (NativeEightBitCipher.observe (withoutDecision c)).map undoToggle

theorem observe_control (c : Configuration) (pc : ℕ) :
    observe {c with pc := pc, halted := true} = observe c := rfl

theorem withoutDecision_equivalent (c d : Configuration) (h : c.Equivalent d) :
    (withoutDecision c).Equivalent (withoutDecision d) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
  intro i
  simpa only [withoutDecision, List.getD_eq_getElem?_getD, List.getElem?_drop] using h.2.2.2.2.1 (1 + i)

theorem observe_equivalent (c d : Configuration) (h : c.Equivalent d) : observe c = observe d := by
  unfold observe
  rw [NativeControlledCipherInitial.observe_equivalent _ _ (withoutDecision_equivalent c d h)]

theorem caller_law (result : Fin 5 × Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.caller
      ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) 30).map observe =
      PMF.pure (some result) := by
  unfold NativeKeyPairDecisionExecution.caller
  change (evalConfigWithin (NativeCiphertextToggle.code.followedBy NativeKeyPairObserver.code)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := some result.2 :: []}) (6 + 23 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 6 23 NativeCiphertextToggle.stops NativeKeyPairObserver.stops,
    NativeCiphertextToggle.run _ {} result.2, PMF.pure_bind]
  change ((evalConfigWithin NativeKeyPairObserver.code
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := some (!result.2) :: []}) 23).map _).map _ = _
  rw [NativeKeyPairObserver.run, PMF.pure_map, PMF.pure_map]
  unfold observe
  change PMF.pure ((NativeEightBitCipher.observe
    (NativeCleanEightBitCipher.finish (NativeCiphertextToggle.code.length + NativeKeyPairObserver.code.length + 2)
      (result.1, !result.2) {} {})).map undoToggle) = _
  rw [NativeCleanEightBitCipher.observe_finish]
  simp [undoToggle]

theorem kernel_law (result : Fin 5 × Bool) :
    (NativeCleanCipherContinuation.kernel NativeKeyPairDecisionExecution.caller 30 {} {} result).map observe =
      PMF.pure (some result) := by
  unfold NativeCleanCipherContinuation.kernel
  rw [PMF.map_comp]
  simp only [Function.comp_def, observe_control]
  exact caller_law result

theorem callee_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.code (NativeControlledEightBitCipher.entry v message {} {}) 442).map observe =
      (tableEightBitLaw v message).map some := by
  unfold NativeKeyPairDecisionExecution.code
  rw [NativeCleanCipherContinuation.run _ 30 NativeKeyPairDecisionExecution.caller_stops, PMF.map_bind]
  simp only [kernel_law]
  rfl

theorem source_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.source ((NativePreparedKeyDecision.prepared v message).resumeAt 0) 442).map observe =
      (tableEightBitLaw v message).map some := by
  unfold NativePreparedKeyDecision.source
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.handoff v message) 442 _ observe_equivalent]
  exact callee_law v message

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map observe =
      (tableEightBitLaw v message).map some := by
  unfold NativePreparedKeyDecision.code NativePreparedKeyDecision.entry
  rw [show 930 = 487 + 442 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ NativePreparedKeyDecision.preparation_stops NativePreparedKeyDecision.source_stops]
  change ((evalConfigWithin NativePreparedKeyDecision.preparation (NativePreparedKeyDecision.entry v message) 487).bind _).map observe = _
  rw [NativePreparedKeyDecision.preparation_run, PMF.pure_bind, PMF.map_comp]
  simp only [Function.comp_def, observe_control]
  exact source_law v message

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map observe =
      (tableEightBitLaw v message).map some := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    930 _ observe_equivalent]
  exact framed_law v message

theorem atom_probability (v : OrderedGridVertex 32) (message : Bool) (result : Fin 5 × Bool) :
    (eventProb ((evalConfigWithin NativePreparedKeyDecision.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map observe) (· = some result)).toReal =
      (eventProb (tableEightBitLaw v message) (· = result)).toReal := by
  rw [initial_law, eventProb_map]
  simp only [Option.some.injEq]

noncomputable def jointDistance (u v : OrderedGridVertex 32) (message : Bool) : ℝ :=
  (∑ key : Fin 5,
    (|(eventProb ((evalConfigWithin NativePreparedKeyDecision.code
        (Configuration.initial (NativePreparedKeyDecision.rawInput u message)) 930).map observe)
        (· = some (key, false))).toReal -
      (eventProb ((evalConfigWithin NativePreparedKeyDecision.code
        (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map observe)
        (· = some (key, false))).toReal| +
     |(eventProb ((evalConfigWithin NativePreparedKeyDecision.code
        (Configuration.initial (NativePreparedKeyDecision.rawInput u message)) 930).map observe)
        (· = some (key, true))).toReal -
      (eventProb ((evalConfigWithin NativePreparedKeyDecision.code
        (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map observe)
        (· = some (key, true))).toReal|)) / 2

theorem jointDistance_eq (u v : OrderedGridVertex 32) (message : Bool) :
    jointDistance u v message = tableEightBitJointDistance u v message := by
  unfold jointDistance tableEightBitJointDistance
  simp only [atom_probability]

theorem edge_bound (u v : OrderedGridVertex 32) (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    jointDistance u v message ≤ 37 / 128 := by
  rw [jointDistance_eq]
  exact table_experiment_edge_upper u v edge message

theorem maximum_attained (message : Bool) :
    jointDistance (sharpTableChain 0) (sharpTableChain 2) message = 37 / 128 := by
  rw [jointDistance_eq, tableEightBitJointDistance_eq_jointTV, sharpTableChain_jointTV]

theorem perfect_four_key_gap (d : OrderedGridVertex 32 → PerfectCipher (Fin 4))
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) → (d v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      jointDistance u v message + 145 / 384 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨u, v, edge, hgap⟩ := table_experiment_perfect_gap d boundary
  exact ⟨u, v, edge, fun message => by rw [jointDistance_eq]; exact hgap message⟩

noncomputable def comparisonDistance (u v : OrderedGridVertex 32) : ℝ :=
  max (jointDistance u v false) (jointDistance u v true)

theorem comparisonDistance_eq (u v : OrderedGridVertex 32) :
    comparisonDistance u v = tableEightBitImplementationDistance u v := by
  unfold comparisonDistance tableEightBitImplementationDistance
  rw [jointDistance_eq, jointDistance_eq]

theorem approximate_four_key_gap (c : OrderedGridVertex 32 → Cipher (Fin 4))
    (ε δ : OrderedGridVertex 32 → ℝ)
    (h0 : ∀ v, ∑ k, (c v).weight k * error0 (c v) k ≤ δ v)
    (h1 : ∀ v, ∑ k, (c v).weight k * error1 (c v) k ≤ δ v)
    (hp : ∀ v, |bias (signedContrast (c v))| ≤ ε v)
    (hm : ∀ v, ε v + 2 * δ v ≤ 1 / 8)
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      repair (signedContrast (c v)) = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      comparisonDistance u v + 1 / 384 ≤ implementationDistance (c u) (c v) := by
  obtain ⟨u, v, edge, hgap⟩ := table_experiment_approximate_gap c ε δ h0 h1 hp hm boundary
  exact ⟨u, v, edge, by rw [comparisonDistance_eq]; exact hgap⟩

end Machine.NativePreparedInternalResult
