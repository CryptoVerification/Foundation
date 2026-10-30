import Foundation.Crypto.Semantics.Machine.NativeReferenceCycleRecovery
import Foundation.Crypto.Semantics.Machine.NativeCanonicalFairRecovery

/-! Every locally edited roundtrip runs after the original cipher and before
the charged packet-restoring caller. A charged stationary comparator reaches
the same actual control. This is final-state equality, not timing equality. -/
namespace Machine.NativeCanonicalCycleRecovery
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open NativeCanonicalFairRecovery (callerKernelAt callerKernelAt_clean positive_halt_stops)
noncomputable section
attribute [local irreducible] NativeReferenceCycleRecovery.code NativePreparedKeyDecision.code

noncomputable def code (r : Fin 95) : Program := (NativeReferenceCycleRecovery.code r).followedBy NativeKeyPairDecisionExecution.caller
noncomputable def padding (r : Fin 95) : Program := List.replicate
  ((NativeReferenceCycleRecovery.continuation r).length + NativeKeyPairDecisionExecution.caller.length + 3) .halt
noncomputable def stationaryCode (r : Fin 95) : Program := NativePreparedKeyDecision.code.followedBy (padding r)

theorem padding_stops (r : Fin 95) : StopsEverywhere (padding r) 1 := by
  rw [padding]
  exact positive_halt_stops _ (by omega)

theorem final_control_equal (r : Fin 95) :
    (NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 2 =
      NativePreparedKeyDecision.code.length + (padding r).length + 2 := by
  have base : (NativeReferenceCycleRecovery.code r).length =
      NativePreparedKeyDecision.code.length + (NativeReferenceCycleRecovery.continuation r).length + 3 := by
    rw [NativeReferenceCycleRecovery.code,NativeUniformSequence.code_length]
  have pad : (padding r).length = (NativeReferenceCycleRecovery.continuation r).length + NativeKeyPairDecisionExecution.caller.length + 3 := by
    rw [padding,List.length_replicate]
  calc
    _ = NativePreparedKeyDecision.code.length + (NativeReferenceCycleRecovery.continuation r).length + 3 +
        NativeKeyPairDecisionExecution.caller.length + 2 := congrArg (fun n => n + NativeKeyPairDecisionExecution.caller.length + 2) base
    _ = NativePreparedKeyDecision.code.length +
        ((NativeReferenceCycleRecovery.continuation r).length + NativeKeyPairDecisionExecution.caller.length + 3) + 2 := by omega
    _ = NativePreparedKeyDecision.code.length + (padding r).length + 2 :=
      (congrArg (fun n => NativePreparedKeyDecision.code.length + n + 2) pad).symm

theorem clean_source_law (r : Fin 95) (message : Bool) :
    (evalConfigWithin (NativeReferenceCycleRecovery.code r)
      (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1645).map NativePreparedState.state =
      (tableEightBitLaw RecoveryRigidity.source message).map
        (NativeReferenceFairRecovery.cleanEncode (NativePreparedKeyDecision.code.length + (NativeReferenceCycleRecovery.continuation r).length + 2)) := by
  rw [(NativeReferenceCycleRecovery.initial_law r),PMF.bind_map]
  simp only [Function.comp_def,(NativeReferenceCycleRecovery.kernelAt_encode r)]
  have h := congrArg (PMF.map (NativeReferenceFairRecovery.cleanEncode
    (NativePreparedKeyDecision.code.length + (NativeReferenceCycleRecovery.continuation r).length + 2)))
      (NativeCycleKernelSampler.loop_joint_preserves r message)
  rw [PMF.map_bind] at h
  simpa only [PMF.map_comp,Function.comp_def] using h

theorem transformed_law (r : Fin 95) (message : Bool) :
    (evalConfigWithin (code r) (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1676).map
      NativePreparedState.state = (tableEightBitLaw RecoveryRigidity.source message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish ((NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 2) result)) := by
  unfold code
  change (evalConfigWithin ((NativeReferenceCycleRecovery.code r).followedBy NativeKeyPairDecisionExecution.caller)
    (NativeBitChoice.start (Tape.ofBits (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) {}) (1645 + 30 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 1645 30 (NativeReferenceCycleRecovery.stops r) NativeKeyPairDecisionExecution.caller_stops,PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin (NativeReferenceCycleRecovery.code r)
    (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1645).bind
      (callerKernelAt ((NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 2) ∘ NativePreparedState.state) = _
  rw [← PMF.bind_map,(clean_source_law r),PMF.bind_map]
  simp only [Function.comp_def,callerKernelAt_clean]
  rfl

theorem stationary_framed_law (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (stationaryCode r) (NativePreparedKeyDecision.entry v message) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + (padding r).length + 2) result)) := by
  unfold stationaryCode NativePreparedKeyDecision.entry
  rw [show 932 = 930 + 1 + 1 from rfl,
    NativeUniformSequence.run _ _ 930 1 NativePreparedKeyDecision.stops (padding_stops r),PMF.map_bind]
  simp only [PMF.map_comp]
  have pad_run (c : Configuration) : evalConfigWithin (padding r) (c.resumeAt 0) 1 =
      PMF.pure {c with pc := 0,halted := true} := by
    have generic (n : Nat) (positive : 0 < n) : evalConfigWithin (List.replicate n .halt) (c.resumeAt 0) 1 =
        PMF.pure {c with pc := 0,halted := true} := by
      cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ,evalConfigWithin,stepPMF,next,Configuration.resumeAt,Instruction.next]
    simpa only [padding] using generic
      ((NativeReferenceCycleRecovery.continuation r).length + NativeKeyPairDecisionExecution.caller.length + 3) (by omega)
  simp only [pad_run,PMF.pure_map]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map
    (atControl (NativePreparedKeyDecision.code.length + (padding r).length + 2)) = _
  have h := congrArg (fun law => law.map (Quotient.lift
    (fun c => atControl (NativePreparedKeyDecision.code.length + (padding r).length + 2) c)
    (atControl_equivalent (NativePreparedKeyDecision.code.length + (padding r).length + 2)))) (NativePreparedState.framed_law v message)
  rw [PMF.map_comp,PMF.map_comp] at h
  exact h

theorem stationary_initial_law (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (stationaryCode r) (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + (padding r).length + 2) result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    932 _ NativePreparedState.state_equivalent]
  exact (stationary_framed_law r) v message

theorem full_cell_identity (r : Fin 95) (message : Bool) :
    (evalConfigWithin (code r) (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1676).map NativePreparedState.state =
      (evalConfigWithin (stationaryCode r) (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 932).map NativePreparedState.state := by
  rw [(transformed_law r),(stationary_initial_law r)]
  exact congrArg (fun pc => (tableEightBitLaw RecoveryRigidity.source message).map
    (fun result => NativePreparedState.state (NativePreparedState.finish pc result))) (final_control_equal r)

theorem stops (r : Fin 95) : StopsEverywhere (code r) 1676 :=
  NativeUniformSequence.stops _ _ 1645 30 (NativeReferenceCycleRecovery.stops r) NativeKeyPairDecisionExecution.caller_stops

theorem stationary_stops (r : Fin 95) : StopsEverywhere (stationaryCode r) 932 :=
  NativeUniformSequence.stops _ _ 930 1 NativePreparedKeyDecision.stops (padding_stops r)

theorem code_length (r : Fin 95) :
    (code r).length ≤ NativePreparedKeyDecision.code.length + 1971577 + NativeKeyPairDecisionExecution.caller.length := by
  have bound := NativeReferenceCycleRecovery.code_length r
  have size : (code r).length = (NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 3 :=
    NativeUniformSequence.code_length _ _
  calc
    (code r).length = (NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 3 := size
    _ ≤ NativePreparedKeyDecision.code.length + 1971577 + NativeKeyPairDecisionExecution.caller.length := by omega

theorem stationary_code_length_eq (r : Fin 95) : (stationaryCode r).length = (code r).length := by
  have actual : (code r).length = (NativeReferenceCycleRecovery.code r).length + NativeKeyPairDecisionExecution.caller.length + 3 :=
    NativeUniformSequence.code_length _ _
  have stationary : (stationaryCode r).length = NativePreparedKeyDecision.code.length + (padding r).length + 3 :=
    NativeUniformSequence.code_length _ _
  have same := final_control_equal r
  omega

theorem stationary_code_length (r : Fin 95) :
    (stationaryCode r).length ≤ NativePreparedKeyDecision.code.length + 1971577 + NativeKeyPairDecisionExecution.caller.length := by
  rw [stationary_code_length_eq]
  exact code_length r

theorem haltsWithin (r : Fin 95) (input : List Bool) : HaltsWithin (code r) input 1676 := (stops r) (Tape.ofBits input) {}
theorem stationary_haltsWithin (r : Fin 95) (input : List Bool) : HaltsWithin (stationaryCode r) input 932 := (stationary_stops r) (Tape.ofBits input) {}

noncomputable def bounded (r : Fin 95) : CryptoLogic.BoundedProgram where
  program := (code r)
  budget := fun _ => 1676
  polynomial := PolynomiallyBounded.const 1676
  halts := (haltsWithin r)
noncomputable def stationaryBounded (r : Fin 95) : CryptoLogic.BoundedProgram where
  program := (stationaryCode r)
  budget := fun _ => 932
  polynomial := PolynomiallyBounded.const 932
  halts := (stationary_haltsWithin r)

theorem polynomial_time (r : Fin 95) : PolynomialTime (code r) := ⟨fun _ => 1676,PolynomiallyBounded.const _,(haltsWithin r)⟩
theorem stationary_polynomial_time (r : Fin 95) : PolynomialTime (stationaryCode r) := ⟨fun _ => 932,PolynomiallyBounded.const _,(stationary_haltsWithin r)⟩

theorem public_identity (r : Fin 95) (message : Bool) :
    evalWithin (code r) (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message) 1676 =
      evalWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message) 930 := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 1676 ((haltsWithin r) _),
    NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 930 (NativePreparedKeyDecision.haltsWithin _)]
  have ht := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView) ((transformed_law r) message)
  have hs := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView)
    (NativePreparedState.initial_law RecoveryRigidity.source message)
  rw [PMF.map_comp,PMF.map_comp] at ht hs
  simp only [Function.comp_def,NativeCanonicalCouplingExecution.outputView_finish,NativeCanonicalCouplingExecution.outputView_encode] at ht hs
  exact ht.trans hs.symm

end
end Machine.NativeCanonicalCycleRecovery
