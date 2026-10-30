import Foundation.Crypto.Semantics.Machine.NativeReferenceFairRequest
import Foundation.Crypto.Semantics.Machine.NativeReferenceFairRecovery
import Foundation.Crypto.Semantics.Machine.NativeCycleKernelSampler

/-! Connect the original 930-step cipher to every locally generated five-state
roundtrip. The 50-step native request adapter and 663-step two-stage sampler
are charged. Full laws use actual control and every tape cell modulo blanks. -/
namespace Machine.NativeReferenceCycleRecovery
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section
attribute [local irreducible] NativePreparedKeyDecision.code NativeCycleKernelSampler.loopCode

noncomputable def continuation (r : Fin 95) : Program := NativeReferenceFairRequest.code.followedBy (NativeCycleKernelSampler.loopCode r)
noncomputable def code (r : Fin 95) : Program := NativePreparedKeyDecision.code.followedBy (continuation r)

abbrev cleanEncode := NativeReferenceFairRecovery.cleanEncode

theorem prepared_run (r : Fin 95) (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (evalConfigWithin (NativeCycleKernelSampler.loopCode r)
      ((NativeReferenceFairRequest.prepared oldPc (NativeEightBitCipher.encodeKey result.1) result.2).resumeAt 0) 663).map (atControl pc) =
      (((CycleKernels.kernel r) result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeReferenceFairRequest.prepared_equivalent oldPc result.1 result.2) 663 _ (atControl_equivalent pc)]
  rw [NativeCycleKernelSampler.loopCode]
  have h := NativeContinuingFiveStateSampler.run_at (NativeCycleKernelSampler.draw r) FairRecovery.sampleReverse
    pc result.1 result.2 (List.replicate 30 none) [none,none]
  rw [NativeCycleKernelSampler.kernel_eq,NativeCycleKernelSampler.reverse_kernel] at h
  exact h


theorem continuation_run (r : Fin 95) (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (evalConfigWithin (continuation r) ((NativePreparedState.finish oldPc result).resumeAt 0) 714).map (atControl pc) =
      (((CycleKernels.kernel r) result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  unfold continuation
  change (evalConfigWithin (NativeReferenceFairRequest.code.followedBy (NativeCycleKernelSampler.loopCode r))
    (NativeBitChoice.start (NativePreparedState.finish oldPc result).inputTape
      (NativePreparedState.finish oldPc result).outputTape) (50 + 663 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 50 663 NativeReferenceFairRequest.stops (NativeCycleKernelSampler.loop_stops r)]
  change ((evalConfigWithin NativeReferenceFairRequest.code ((NativePreparedState.finish oldPc result).resumeAt 0) 50).bind _).map _ = _
  rw [NativeReferenceFairRequest.run,PMF.pure_bind,PMF.map_comp]
  exact (prepared_run r) pc _ result

noncomputable def kernelAt (r : Fin 95) (pc : Nat) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin (continuation r) (c.resumeAt 0) 714).map (atControl pc)) (by
    intro c d h
    exact evalConfigWithin_map_eq_of_equivalent _ _ _
      (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 714 _ (atControl_equivalent pc))

theorem kernelAt_finish (r : Fin 95) (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (kernelAt r) pc (NativePreparedState.state (NativePreparedState.finish oldPc result)) =
      (((CycleKernels.kernel r) result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) :=
  (continuation_run r) pc oldPc result

theorem kernelAt_encode (r : Fin 95) (pc : Nat) (result : Fin 5 × Bool) :
    (kernelAt r) pc (NativePreparedState.encode result) =
      (((CycleKernels.kernel r) result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  rw [NativePreparedState.encode,(kernelAt_finish r)]

theorem continuation_stops (r : Fin 95) : StopsEverywhere (continuation r) 714 :=
  NativeUniformSequence.stops _ _ 50 663 NativeReferenceFairRequest.stops (NativeCycleKernelSampler.loop_stops r)

theorem framed_law (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (code r) (NativePreparedKeyDecision.entry v message) 1645).map NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        ((kernelAt r) (NativePreparedKeyDecision.code.length + (continuation r).length + 2)) := by
  unfold code NativePreparedKeyDecision.entry
  rw [show 1645 = 930 + 714 + 1 from rfl,
    NativeUniformSequence.run NativePreparedKeyDecision.code (continuation r) 930 714
      NativePreparedKeyDecision.stops (continuation_stops r),PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).bind
    ((kernelAt r) (NativePreparedKeyDecision.code.length + (continuation r).length + 2) ∘ NativePreparedState.state) = _
  rw [← PMF.bind_map,NativePreparedState.framed_law]

theorem initial_law (r : Fin 95) (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (code r) (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 1645).map NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        ((kernelAt r) (NativePreparedKeyDecision.code.length + (continuation r).length + 2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    1645 _ NativePreparedState.state_equivalent]
  exact (framed_law r) v message

theorem stops (r : Fin 95) : StopsEverywhere (code r) 1645 :=
  NativeUniformSequence.stops _ _ 930 714 NativePreparedKeyDecision.stops (continuation_stops r)

theorem continuation_length (r : Fin 95) : (continuation r).length ≤ 1971571 := by
  have a := NativeReferenceFairRequest.code_length
  have recoverySize := NativeCycleKernelSampler.loop_length r
  have size : (continuation r).length = NativeReferenceFairRequest.code.length + (NativeCycleKernelSampler.loopCode r).length + 3 := by
    change (NativeReferenceFairRequest.code.followedBy (NativeCycleKernelSampler.loopCode r)).length = _
    exact NativeUniformSequence.code_length _ _
  calc
    (continuation r).length = NativeReferenceFairRequest.code.length + (NativeCycleKernelSampler.loopCode r).length + 3 := size
    _ ≤ 1971571 := by omega

theorem code_length (r : Fin 95) : (code r).length ≤ NativePreparedKeyDecision.code.length + 1971574 := by
  have h := (continuation_length r)
  have size : (code r).length = NativePreparedKeyDecision.code.length + (continuation r).length + 3 := by
    change (NativePreparedKeyDecision.code.followedBy (continuation r)).length = _
    exact NativeUniformSequence.code_length _ _
  calc
    (code r).length = NativePreparedKeyDecision.code.length + (continuation r).length + 3 := size
    _ ≤ NativePreparedKeyDecision.code.length + 1971574 := by omega

theorem haltsWithin (r : Fin 95) (input : List Bool) : HaltsWithin (code r) input 1645 := (stops r) (Tape.ofBits input) {}

noncomputable def bounded (r : Fin 95) : CryptoLogic.BoundedProgram where
  program := (code r)
  budget := fun _ => 1645
  polynomial := PolynomiallyBounded.const 1645
  halts := (haltsWithin r)

theorem polynomial_time (r : Fin 95) : PolynomialTime (code r) := ⟨fun _ => 1645,PolynomiallyBounded.const _,(haltsWithin r)⟩

end
end Machine.NativeReferenceCycleRecovery
