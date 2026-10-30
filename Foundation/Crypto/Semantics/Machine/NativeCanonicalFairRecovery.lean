import Foundation.Crypto.Semantics.Machine.NativeReferenceFairRecovery
import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecoveryCipher
import Foundation.Crypto.Semantics.Machine.NativeCanonicalCouplingExecution

/-! Restore the native reference packet with the existing 30-step caller.
The fair loop and a charged stationary reference end at a common real control
position. Final-state laws agree; this does not make conditional recovery exact. -/
namespace Machine.NativeCanonicalFairRecovery
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section
attribute [local irreducible] NativeReferenceFairRecovery.code NativePreparedKeyDecision.code

theorem keep_blank (keep : List (Option Bool)) (n : Nat) :
    ({left := keep ++ List.replicate n none} : Tape).Equivalent {left := keep} := by
  induction keep with
  | nil => exact NativeAdaptedRecoverableCoupling.blank_left n
  | cons value keep ih =>
    refine ⟨rfl,?_,fun _ => rfl⟩
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih.2.1 i

theorem clean_equivalent (pc : Nat) (result : Fin 5 × Bool) :
    ((NativeCleanFairRecovery.finish pc result.1 result.2
      {left := List.replicate 19 none ++ List.replicate 30 none} {left := [none,none,none]}).resumeAt 0).Equivalent
      ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · let keep := [some (NativeEightBitCipher.encodeKey result.1 2),some (NativeEightBitCipher.encodeKey result.1 1),
      some (NativeEightBitCipher.encodeKey result.1 0)]
    have h := (keep_blank keep 65).trans (keep_blank keep 27).symm
    have split : List.replicate 65 (none : Option Bool) =
        List.replicate 16 none ++ (List.replicate 19 none ++ List.replicate 30 none) := by decide +kernel
    simpa only [NativeCleanFairRecovery.finish,NativeCleanEightBitCipher.finish,Configuration.resumeAt,
      keep,split,List.cons_append,List.nil_append,List.append_nil,List.append_assoc] using h
  · have h := keep_blank [some result.2] 3
    exact h

theorem caller_run_at (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.caller
      ((NativeCleanFairRecovery.finish oldPc result.1 result.2
        {left := List.replicate 19 none ++ List.replicate 30 none} {left := [none,none,none]}).resumeAt 0) 30).map (atControl pc) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (clean_equivalent oldPc result) 30 _ (atControl_equivalent pc),
    NativePreparedState.caller_run,PMF.pure_map]
  rfl

noncomputable def callerKernelAt (pc : Nat) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin NativeKeyPairDecisionExecution.caller (c.resumeAt 0) 30).map (atControl pc)) (by
    intro c d h
    exact evalConfigWithin_map_eq_of_equivalent _ _ _
      (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 30 _ (atControl_equivalent pc))

theorem callerKernelAt_clean (pc oldPc : Nat) (result : Fin 5 × Bool) :
    callerKernelAt pc (NativeReferenceFairRecovery.cleanEncode oldPc result) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc result)) := caller_run_at pc oldPc result

noncomputable def code : Program := NativeReferenceFairRecovery.code.followedBy NativeKeyPairDecisionExecution.caller
noncomputable def padding : Program := List.replicate
  (NativeReferenceFairRecovery.continuation.length + NativeKeyPairDecisionExecution.caller.length + 3) .halt
noncomputable def stationaryCode : Program := NativePreparedKeyDecision.code.followedBy padding

theorem positive_halt_stops (n : Nat) (positive : 0 < n) : StopsEverywhere (List.replicate n .halt) 1 := by
  cases n with
  | zero => omega
  | succ n => exact NativeCanonicalCouplingExecution.halt_padding_stops n

theorem padding_stops : StopsEverywhere padding 1 := by
  rw [padding]
  exact positive_halt_stops _ (by omega)

theorem final_control_equal :
    NativeReferenceFairRecovery.code.length + NativeKeyPairDecisionExecution.caller.length + 2 =
      NativePreparedKeyDecision.code.length + padding.length + 2 := by
  have base : NativeReferenceFairRecovery.code.length =
      NativePreparedKeyDecision.code.length + NativeReferenceFairRecovery.continuation.length + 3 := by
    rw [NativeReferenceFairRecovery.code,NativeUniformSequence.code_length]
  have pad : padding.length = NativeReferenceFairRecovery.continuation.length + NativeKeyPairDecisionExecution.caller.length + 3 := by
    rw [padding,List.length_replicate]
  calc
    _ = NativePreparedKeyDecision.code.length + NativeReferenceFairRecovery.continuation.length + 3 +
        NativeKeyPairDecisionExecution.caller.length + 2 := congrArg (fun n => n + NativeKeyPairDecisionExecution.caller.length + 2) base
    _ = NativePreparedKeyDecision.code.length +
        (NativeReferenceFairRecovery.continuation.length + NativeKeyPairDecisionExecution.caller.length + 3) + 2 := by omega
    _ = NativePreparedKeyDecision.code.length + padding.length + 2 :=
      (congrArg (fun n => NativePreparedKeyDecision.code.length + n + 2) pad).symm

theorem clean_source_law (message : Bool) :
    (evalConfigWithin NativeReferenceFairRecovery.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1645).map NativePreparedState.state =
      (tableEightBitLaw RecoveryRigidity.source message).map
        (NativeReferenceFairRecovery.cleanEncode (NativePreparedKeyDecision.code.length + NativeReferenceFairRecovery.continuation.length + 2)) := by
  rw [NativeReferenceFairRecovery.initial_law,PMF.bind_map]
  simp only [Function.comp_def,NativeReferenceFairRecovery.kernelAt_encode]
  have h := congrArg (PMF.map (NativeReferenceFairRecovery.cleanEncode
    (NativePreparedKeyDecision.code.length + NativeReferenceFairRecovery.continuation.length + 2)))
      (FairRecoveryCipher.joint_roundtrip_preserve message)
  rw [PMF.map_bind] at h
  simpa only [PMF.map_comp,Function.comp_def] using h

theorem transformed_law (message : Bool) :
    (evalConfigWithin code (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1676).map
      NativePreparedState.state = (tableEightBitLaw RecoveryRigidity.source message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativeReferenceFairRecovery.code.length + NativeKeyPairDecisionExecution.caller.length + 2) result)) := by
  unfold code
  change (evalConfigWithin (NativeReferenceFairRecovery.code.followedBy NativeKeyPairDecisionExecution.caller)
    (NativeBitChoice.start (Tape.ofBits (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) {}) (1645 + 30 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 1645 30 NativeReferenceFairRecovery.stops NativeKeyPairDecisionExecution.caller_stops,PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin NativeReferenceFairRecovery.code
    (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1645).bind
      (callerKernelAt (NativeReferenceFairRecovery.code.length + NativeKeyPairDecisionExecution.caller.length + 2) ∘ NativePreparedState.state) = _
  rw [← PMF.bind_map,clean_source_law,PMF.bind_map]
  simp only [Function.comp_def,callerKernelAt_clean]
  rfl

theorem stationary_framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin stationaryCode (NativePreparedKeyDecision.entry v message) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  unfold stationaryCode NativePreparedKeyDecision.entry
  rw [show 932 = 930 + 1 + 1 from rfl,
    NativeUniformSequence.run _ _ 930 1 NativePreparedKeyDecision.stops padding_stops,PMF.map_bind]
  simp only [PMF.map_comp]
  have pad_run (c : Configuration) : evalConfigWithin padding (c.resumeAt 0) 1 =
      PMF.pure {c with pc := 0,halted := true} := by
    have generic (n : Nat) (positive : 0 < n) : evalConfigWithin (List.replicate n .halt) (c.resumeAt 0) 1 =
        PMF.pure {c with pc := 0,halted := true} := by
      cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ,evalConfigWithin,stepPMF,next,Configuration.resumeAt,Instruction.next]
    simpa only [padding] using generic
      (NativeReferenceFairRecovery.continuation.length + NativeKeyPairDecisionExecution.caller.length + 3) (by omega)
  simp only [pad_run,PMF.pure_map]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map
    (atControl (NativePreparedKeyDecision.code.length + padding.length + 2)) = _
  have h := congrArg (fun law => law.map (Quotient.lift
    (fun c => atControl (NativePreparedKeyDecision.code.length + padding.length + 2) c)
    (atControl_equivalent (NativePreparedKeyDecision.code.length + padding.length + 2)))) (NativePreparedState.framed_law v message)
  rw [PMF.map_comp,PMF.map_comp] at h
  exact h

theorem stationary_initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin stationaryCode (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    932 _ NativePreparedState.state_equivalent]
  exact stationary_framed_law v message

theorem full_cell_identity (message : Bool) :
    (evalConfigWithin code (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 1676).map NativePreparedState.state =
      (evalConfigWithin stationaryCode (Configuration.initial (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message)) 932).map NativePreparedState.state := by
  rw [transformed_law,stationary_initial_law]
  exact congrArg (fun pc => (tableEightBitLaw RecoveryRigidity.source message).map
    (fun result => NativePreparedState.state (NativePreparedState.finish pc result))) final_control_equal

theorem stops : StopsEverywhere code 1676 :=
  NativeUniformSequence.stops _ _ 1645 30 NativeReferenceFairRecovery.stops NativeKeyPairDecisionExecution.caller_stops

theorem stationary_stops : StopsEverywhere stationaryCode 932 :=
  NativeUniformSequence.stops _ _ 930 1 NativePreparedKeyDecision.stops padding_stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 1676 := stops (Tape.ofBits input) {}
theorem stationary_haltsWithin (input : List Bool) : HaltsWithin stationaryCode input 932 := stationary_stops (Tape.ofBits input) {}

noncomputable def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 1676
  polynomial := PolynomiallyBounded.const 1676
  halts := haltsWithin
noncomputable def stationaryBounded : CryptoLogic.BoundedProgram where
  program := stationaryCode
  budget := fun _ => 932
  polynomial := PolynomiallyBounded.const 932
  halts := stationary_haltsWithin

theorem polynomial_time : PolynomialTime code := ⟨fun _ => 1676,PolynomiallyBounded.const _,haltsWithin⟩
theorem stationary_polynomial_time : PolynomialTime stationaryCode := ⟨fun _ => 932,PolynomiallyBounded.const _,stationary_haltsWithin⟩

theorem public_identity (message : Bool) :
    evalWithin code (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message) 1676 =
      evalWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.rawInput RecoveryRigidity.source message) 930 := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 1676 (haltsWithin _),
    NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 930 (NativePreparedKeyDecision.haltsWithin _)]
  have ht := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView) (transformed_law message)
  have hs := congrArg (fun law => law.map NativeCanonicalCouplingExecution.outputView)
    (NativePreparedState.initial_law RecoveryRigidity.source message)
  rw [PMF.map_comp,PMF.map_comp] at ht hs
  simp only [Function.comp_def,NativeCanonicalCouplingExecution.outputView_finish,NativeCanonicalCouplingExecution.outputView_encode] at ht hs
  exact ht.trans hs.symm

end
end Machine.NativeCanonicalFairRecovery
