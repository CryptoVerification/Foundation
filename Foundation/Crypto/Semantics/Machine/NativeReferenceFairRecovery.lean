import Foundation.Crypto.Semantics.Machine.NativeReferenceFairRequest
import Foundation.Crypto.Semantics.Machine.NativeContinuingFairRecovery

/-! The original 930-step cipher and the new fair recovery continuation run
in one program. Entry conversion costs 50 steps; the continuation costs 714
including its connection to the 663-step roundtrip. No stationary comparator
or canonical reference packet conversion is asserted here. -/
namespace Machine.NativeReferenceFairRecovery
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section
attribute [local irreducible] NativePreparedKeyDecision.code NativeContinuingFairRecovery.code

noncomputable def continuation : Program := NativeReferenceFairRequest.code.followedBy NativeContinuingFairRecovery.code
noncomputable def code : Program := NativePreparedKeyDecision.code.followedBy continuation

def cleanEncode (pc : Nat) (result : Fin 5 × Bool) : NativePreparedState.State :=
  NativePreparedState.state (NativeCleanFairRecovery.finish pc result.1 result.2
    {left := List.replicate 19 none ++ List.replicate 30 none} {left := [none,none,none]})

theorem cleanEncode_injective (pc : Nat) : Function.Injective (cleanEncode pc) := by
  intro a b same
  have cells := (NativePreparedState.state_eq_iff _ _).mp same
  have h := NativeControlledCipherInitial.observe_equivalent _ _ cells
  rw [NativeCleanFairRecovery.observe_finish,NativeCleanFairRecovery.observe_finish] at h
  exact Option.some.inj h

theorem prepared_run (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (evalConfigWithin NativeContinuingFairRecovery.code
      ((NativeReferenceFairRequest.prepared oldPc (NativeEightBitCipher.encodeKey result.1) result.2).resumeAt 0) 663).map (atControl pc) =
      ((FairRecovery.forward result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeReferenceFairRequest.prepared_equivalent oldPc result.1 result.2) 663 _ (atControl_equivalent pc)]
  exact NativeContinuingFairRecovery.run_at pc result.1 result.2 (List.replicate 30 none) [none,none]

theorem continuation_run (pc oldPc : Nat) (result : Fin 5 × Bool) :
    (evalConfigWithin continuation ((NativePreparedState.finish oldPc result).resumeAt 0) 714).map (atControl pc) =
      ((FairRecovery.forward result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  unfold continuation
  change (evalConfigWithin (NativeReferenceFairRequest.code.followedBy NativeContinuingFairRecovery.code)
    (NativeBitChoice.start (NativePreparedState.finish oldPc result).inputTape
      (NativePreparedState.finish oldPc result).outputTape) (50 + 663 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 50 663 NativeReferenceFairRequest.stops NativeContinuingFairRecovery.stops]
  change ((evalConfigWithin NativeReferenceFairRequest.code ((NativePreparedState.finish oldPc result).resumeAt 0) 50).bind _).map _ = _
  rw [NativeReferenceFairRequest.run,PMF.pure_bind,PMF.map_comp]
  exact prepared_run pc _ result

noncomputable def kernelAt (pc : Nat) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin continuation (c.resumeAt 0) 714).map (atControl pc)) (by
    intro c d h
    exact evalConfigWithin_map_eq_of_equivalent _ _ _
      (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 714 _ (atControl_equivalent pc))

theorem kernelAt_finish (pc oldPc : Nat) (result : Fin 5 × Bool) :
    kernelAt pc (NativePreparedState.state (NativePreparedState.finish oldPc result)) =
      ((FairRecovery.forward result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) :=
  continuation_run pc oldPc result

theorem kernelAt_encode (pc : Nat) (result : Fin 5 × Bool) :
    kernelAt pc (NativePreparedState.encode result) =
      ((FairRecovery.forward result.1).bind FairRecovery.reverse).map (fun key => cleanEncode pc (key,result.2)) := by
  rw [NativePreparedState.encode,kernelAt_finish]

theorem continuation_stops : StopsEverywhere continuation 714 :=
  NativeUniformSequence.stops _ _ 50 663 NativeReferenceFairRequest.stops NativeContinuingFairRecovery.stops

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (NativePreparedKeyDecision.entry v message) 1645).map NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        (kernelAt (NativePreparedKeyDecision.code.length + continuation.length + 2)) := by
  unfold code NativePreparedKeyDecision.entry
  rw [show 1645 = 930 + 714 + 1 from rfl,
    NativeUniformSequence.run NativePreparedKeyDecision.code continuation 930 714
      NativePreparedKeyDecision.stops continuation_stops,PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).bind
    (kernelAt (NativePreparedKeyDecision.code.length + continuation.length + 2) ∘ NativePreparedState.state) = _
  rw [← PMF.bind_map,NativePreparedState.framed_law]

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 1645).map NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        (kernelAt (NativePreparedKeyDecision.code.length + continuation.length + 2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    1645 _ NativePreparedState.state_equivalent]
  exact framed_law v message

theorem stops : StopsEverywhere code 1645 :=
  NativeUniformSequence.stops _ _ 930 714 NativePreparedKeyDecision.stops continuation_stops

theorem continuation_length : continuation.length ≤ 1971571 := by
  have a := NativeReferenceFairRequest.code_length
  have r := NativeContinuingFairRecovery.code_length
  have size : continuation.length = NativeReferenceFairRequest.code.length + NativeContinuingFairRecovery.code.length + 3 := by
    change (NativeReferenceFairRequest.code.followedBy NativeContinuingFairRecovery.code).length = _
    exact NativeUniformSequence.code_length _ _
  calc
    continuation.length = NativeReferenceFairRequest.code.length + NativeContinuingFairRecovery.code.length + 3 := size
    _ ≤ 1971571 := by omega

theorem code_length : code.length ≤ NativePreparedKeyDecision.code.length + 1971574 := by
  have h := continuation_length
  have size : code.length = NativePreparedKeyDecision.code.length + continuation.length + 3 := by
    change (NativePreparedKeyDecision.code.followedBy continuation).length = _
    exact NativeUniformSequence.code_length _ _
  calc
    code.length = NativePreparedKeyDecision.code.length + continuation.length + 3 := size
    _ ≤ NativePreparedKeyDecision.code.length + 1971574 := by omega

theorem haltsWithin (input : List Bool) : HaltsWithin code input 1645 := stops (Tape.ofBits input) {}

noncomputable def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 1645
  polynomial := PolynomiallyBounded.const 1645
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := ⟨fun _ => 1645,PolynomiallyBounded.const _,haltsWithin⟩

end
end Machine.NativeReferenceFairRecovery
