import Foundation.Crypto.Semantics.Machine.NativeReverseCoupling

/-! Native forward and reverse conditional kernels and their continuing
execution. Recovery is pointwise on the two admitted source states, not just
preservation of the averaged marginal and not identity on arbitrary states. -/
namespace Machine.NativeCompiledRecovery
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def forwardCode : Program := NativeAdaptedRecoverableCoupling.code.followedBy NativeCouplingExitAdapter.code

theorem forward_stops : StopsEverywhere forwardCode 288 :=
  NativeUniformSequence.stops NativeAdaptedRecoverableCoupling.code NativeCouplingExitAdapter.code 258 29
    NativeAdaptedRecoverableCoupling.stops NativeCouplingExitAdapter.stops

def forwardKernelAt (pc : ℕ) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin forwardCode (c.resumeAt 0) 288).map
    (NativeAdaptedRecoverableCoupling.atControl pc)) (by
      intro c d h
      exact evalConfigWithin_map_eq_of_equivalent _ _ _
        (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 288 _
          (NativeAdaptedRecoverableCoupling.atControl_equivalent pc))

theorem forward_composition (pc : ℕ) (c : Configuration) :
    (evalConfigWithin forwardCode (c.resumeAt 0) 288).map (NativeAdaptedRecoverableCoupling.atControl pc) =
      ((evalConfigWithin NativeAdaptedRecoverableCoupling.code (c.resumeAt 0) 258).map
        (NativeAdaptedRecoverableCoupling.atControl 0)).bind (NativeCouplingExitAdapter.kernelAt pc) := by
  unfold forwardCode
  change (evalConfigWithin (NativeAdaptedRecoverableCoupling.code.followedBy NativeCouplingExitAdapter.code)
    (NativeBitChoice.start c.inputTape c.outputTape) (258 + 29 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 258 29 NativeAdaptedRecoverableCoupling.stops NativeCouplingExitAdapter.stops,
    PMF.map_bind, PMF.bind_map]
  simp only [PMF.map_comp]
  rfl

theorem forward_source (pc : ℕ) (message bit : Bool) :
    forwardKernelAt pc (NativePreparedState.encode (Recoverable.sourceResult message bit)) =
      (Recoverable.forward bit).map (fun key => NativePreparedState.state
        (NativePreparedState.finish pc (Recoverable.targetResult message key))) := by
  change (evalConfigWithin forwardCode
    ((NativePreparedState.finish _ (Recoverable.sourceResult message bit)).resumeAt 0) 288).map _ = _
  rw [forward_composition]
  change (NativeAdaptedRecoverableCoupling.kernelAt 0
    (NativePreparedState.encode (Recoverable.sourceResult message bit))).bind _ = _
  rw [NativeReferenceCouplingExecution.source_kernel, PMF.bind_map]
  simp only [Function.comp_def, NativeCouplingExitAdapter.kernelAt_clean]
  rfl

def roundtripCode : Program := forwardCode.followedBy NativeReverseCoupling.code

theorem roundtrip_stops : StopsEverywhere roundtripCode 390 :=
  NativeUniformSequence.stops forwardCode NativeReverseCoupling.code 288 101
    forward_stops NativeReverseCoupling.stops

def roundtripKernelAt (pc : ℕ) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin roundtripCode (c.resumeAt 0) 390).map
    (NativeAdaptedRecoverableCoupling.atControl pc)) (by
      intro c d h
      exact evalConfigWithin_map_eq_of_equivalent _ _ _
        (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 390 _
          (NativeAdaptedRecoverableCoupling.atControl_equivalent pc))

theorem roundtrip_composition (pc : ℕ) (c : Configuration) :
    (evalConfigWithin roundtripCode (c.resumeAt 0) 390).map (NativeAdaptedRecoverableCoupling.atControl pc) =
      ((evalConfigWithin forwardCode (c.resumeAt 0) 288).map
        (NativeAdaptedRecoverableCoupling.atControl 0)).bind (NativeReverseCoupling.kernelAt pc) := by
  unfold roundtripCode
  change (evalConfigWithin (forwardCode.followedBy NativeReverseCoupling.code)
    (NativeBitChoice.start c.inputTape c.outputTape) (288 + 101 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 288 101 forward_stops NativeReverseCoupling.stops,
    PMF.map_bind, PMF.bind_map]
  simp only [PMF.map_comp, Function.comp_def, NativeReverseCoupling.kernelAt,
    NativeAdaptedRecoverableCoupling.atControl, NativePreparedState.state,
    Configuration.resumeAt]
  rfl

theorem roundtrip_source (pc : ℕ) (message bit : Bool) :
    roundtripKernelAt pc (NativePreparedState.encode (Recoverable.sourceResult message bit)) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc (Recoverable.sourceResult message bit))) := by
  change (evalConfigWithin roundtripCode
    ((NativePreparedState.finish _ (Recoverable.sourceResult message bit)).resumeAt 0) 390).map _ = _
  rw [roundtrip_composition]
  change (forwardKernelAt 0 (NativePreparedState.encode (Recoverable.sourceResult message bit))).bind _ = _
  rw [forward_source, PMF.bind_map]
  simp only [Function.comp_def, NativeReverseCoupling.kernelAt_target]
  have h := congrArg (fun law : PMF Bool => law.map (fun b => NativePreparedState.state
    (NativePreparedState.finish pc (Recoverable.sourceResult message b)))) (Recoverable.recovers bit)
  rw [PMF.map_comp, PMF.pure_map] at h
  exact h

def code : Program := NativePreparedKeyDecision.code.followedBy roundtripCode

theorem raw_law (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1321).map
      NativePreparedState.state =
      (Roundtrip.p message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + roundtripCode.length + 2) result)) := by
  have framed : (evalConfigWithin code (NativePreparedKeyDecision.entry (sharpTableChain 0) message) 1321).map
      NativePreparedState.state =
      (Roundtrip.p message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + roundtripCode.length + 2) result)) := by
    unfold code NativePreparedKeyDecision.entry
    rw [show 1321 = 930 + 390 + 1 from rfl,
      NativeUniformSequence.run _ _ 930 390 NativePreparedKeyDecision.stops roundtrip_stops, PMF.map_bind]
    simp only [PMF.map_comp]
    change (evalConfigWithin NativePreparedKeyDecision.code
      (NativePreparedKeyDecision.entry (sharpTableChain 0) message) 930).bind
        (roundtripKernelAt (NativePreparedKeyDecision.code.length + roundtripCode.length + 2) ∘
          NativePreparedState.state) = _
    rw [← PMF.bind_map, NativePreparedState.framed_law]
    change ((Roundtrip.p message).map NativePreparedState.encode).bind _ = _
    simp only [← Recoverable.source_law message]
    rw [PMF.map_comp, PMF.map_comp, PMF.bind_map]
    simp only [Function.comp_def, roundtrip_source]
    rfl
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativePreparedKeyDecision.entry_equivalent (sharpTableChain 0) message).symm 1321 _ NativePreparedState.state_equivalent]
  exact framed

theorem stops : StopsEverywhere code 1321 :=
  NativeUniformSequence.stops NativePreparedKeyDecision.code roundtripCode 930 390
    NativePreparedKeyDecision.stops roundtrip_stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 1321 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 1321
  polynomial := PolynomiallyBounded.const 1321
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem roundtrip_code_length : roundtripCode.length ≤ 9064 := by
  have ha := NativeAdaptedRecoverableCoupling.code_length
  have he := NativeCouplingExitAdapter.code_length
  have hr := NativeReverseCoupling.code_length
  rw [roundtripCode, forwardCode, NativeUniformSequence.code_length, NativeUniformSequence.code_length]
  omega

end
end Machine.NativeCompiledRecovery
