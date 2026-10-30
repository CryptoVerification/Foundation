import Foundation.Crypto.Semantics.Machine.NativeCompiledRecovery

/-! The actual raw reference experiment followed by native forward/reverse
recovery equals a stationary reference execution with a charged common halt
position, including all cells and control. Public equality also holds against
the original unwrapped reference. -/
namespace Machine.NativeRecoveryIdentity
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def padding : Program := List.replicate
  (NativeCompiledRecovery.forwardCode.length + NativeReverseCoupling.code.length + 2 + 1) .halt
def stationaryCode : Program := NativePreparedKeyDecision.code.followedBy padding

theorem padding_stops : StopsEverywhere padding 1 := NativeCanonicalCouplingExecution.halt_padding_stops _

theorem final_control_equal :
    NativePreparedKeyDecision.code.length + NativeCompiledRecovery.roundtripCode.length + 2 =
      NativePreparedKeyDecision.code.length + padding.length + 2 := by
  have length : NativeCompiledRecovery.roundtripCode.length = padding.length := by
    rw [NativeCompiledRecovery.roundtripCode, NativeUniformSequence.code_length, padding, List.length_replicate]
  exact congrArg (fun n => NativePreparedKeyDecision.code.length + n + 2) length

theorem stationary_framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin stationaryCode (NativePreparedKeyDecision.entry v message) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  unfold stationaryCode NativePreparedKeyDecision.entry
  rw [show 932 = 930 + 1 + 1 from rfl,
    NativeUniformSequence.run _ _ 930 1 NativePreparedKeyDecision.stops padding_stops, PMF.map_bind]
  simp only [PMF.map_comp]
  have pad_run (c : Configuration) : evalConfigWithin padding (c.resumeAt 0) 1 =
      PMF.pure {c with pc := 0, halted := true} := by
    have generic (n : ℕ) : evalConfigWithin (List.replicate (n + 1) .halt) (c.resumeAt 0) 1 =
        PMF.pure {c with pc := 0, halted := true} := by
      simp [List.replicate_succ, evalConfigWithin, stepPMF, next, Configuration.resumeAt, Instruction.next]
    exact generic _
  simp only [pad_run, PMF.pure_map]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map
    (NativeAdaptedRecoverableCoupling.atControl (NativePreparedKeyDecision.code.length + padding.length + 2)) = _
  have h := congrArg (fun law => law.map (Quotient.lift
    (fun c => NativeAdaptedRecoverableCoupling.atControl (NativePreparedKeyDecision.code.length + padding.length + 2) c)
    (NativeAdaptedRecoverableCoupling.atControl_equivalent
      (NativePreparedKeyDecision.code.length + padding.length + 2)))) (NativePreparedState.framed_law v message)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

theorem stationary_initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin stationaryCode (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 932).map
      NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativePreparedKeyDecision.entry_equivalent v message).symm 932 _ NativePreparedState.state_equivalent]
  exact stationary_framed_law v message

theorem full_cell_identity (message : Bool) :
    (evalConfigWithin NativeCompiledRecovery.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1321).map
      NativePreparedState.state =
    (evalConfigWithin stationaryCode
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 932).map
      NativePreparedState.state := by
  rw [NativeCompiledRecovery.raw_law, stationary_initial_law, final_control_equal]
  rfl

theorem stationary_stops : StopsEverywhere stationaryCode 932 :=
  NativeUniformSequence.stops NativePreparedKeyDecision.code padding 930 1 NativePreparedKeyDecision.stops padding_stops

theorem stationary_haltsWithin (input : List Bool) : HaltsWithin stationaryCode input 932 :=
  stationary_stops (Tape.ofBits input) {}

def stationaryBounded : CryptoLogic.BoundedProgram where
  program := stationaryCode
  budget := fun _ => 932
  polynomial := PolynomiallyBounded.const 932
  halts := stationary_haltsWithin

theorem public_identity (message : Bool) :
    evalWithin NativeCompiledRecovery.code (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message) 1321 =
      evalWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message) 930 := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 1321 (NativeCompiledRecovery.haltsWithin _),
    NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 930 (NativePreparedKeyDecision.haltsWithin _)]
  have ht := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView) (NativeCompiledRecovery.raw_law message)
  have hs := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView)
    (NativePreparedState.initial_law (sharpTableChain 0) message)
  rw [PMF.map_comp, PMF.map_comp] at ht hs
  simp only [Function.comp_def, NativeCanonicalCouplingExecution.outputView_finish,
    NativeCanonicalCouplingExecution.outputView_encode] at ht hs
  exact ht.trans hs.symm

end
end Machine.NativeRecoveryIdentity
