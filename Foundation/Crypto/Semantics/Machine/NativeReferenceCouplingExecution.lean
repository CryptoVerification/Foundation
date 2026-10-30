import Foundation.Crypto.Semantics.Machine.NativeAdaptedRecoverableCoupling

/-! A single raw-input native execution runs the 930-step reference experiment,
then the 258-step request adapter and cleaned repaired coupling. Its full-cell
exit law is the target experiment in a new, explicitly stated clean layout.
No canonical reference-exit adapter or general coherence family is claimed. -/
namespace Machine.NativeReferenceCouplingExecution
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def code : Program := NativePreparedKeyDecision.code.followedBy NativeAdaptedRecoverableCoupling.code

def cleanEncode (pc : ℕ) (result : Fin 5 × Bool) : NativePreparedState.State :=
  NativePreparedState.state (NativeCleanRecoverableCoupling.finish pc
    (Recoverable.parent result.1) result.2 result.1 {} {})

theorem cleanEncode_injective (pc : ℕ) : Function.Injective (cleanEncode pc) := by
  intro a b same
  have cells := (NativePreparedState.state_eq_iff _ _).mp same
  have h := NativeRecoverableCouplingExecution.observe_equivalent _ _ cells
  rw [NativeCleanRecoverableCoupling.observe_finish, NativeCleanRecoverableCoupling.observe_finish] at h
  exact Option.some.inj (congrArg Prod.fst h)

theorem source_parent (message bit : Bool) :
    Recoverable.parent (Recoverable.sourceResult message bit).1 = bit := by
  cases bit <;> rfl

theorem source_kernel (pc : ℕ) (message bit : Bool) :
    NativeAdaptedRecoverableCoupling.kernelAt pc (NativePreparedState.encode (Recoverable.sourceResult message bit)) =
      (Recoverable.forward bit).map (fun key => cleanEncode pc (Recoverable.targetResult message key)) := by
  rw [NativePreparedState.encode, NativeAdaptedRecoverableCoupling.kernelAt_finish, source_parent]
  change (Recoverable.forward bit).bind (fun key => PMF.pure (NativePreparedState.state
      (NativeCleanRecoverableCoupling.finish pc bit (Recoverable.sourceResult message bit).2 key {} {}))) =
    (Recoverable.forward bit).bind (fun key => PMF.pure (cleanEncode pc (Recoverable.targetResult message key)))
  apply bind_congr_of_support
  intro key supported
  have parent := Recoverable.parent_supported bit key supported
  cases bit <;> simp [cleanEncode, Recoverable.sourceResult, Recoverable.targetResult, parent]

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (NativePreparedKeyDecision.entry v message) 1189).map NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        (NativeAdaptedRecoverableCoupling.kernelAt
          (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2)) := by
  unfold code NativePreparedKeyDecision.entry
  rw [show 1189 = 930 + 258 + 1 from rfl,
    NativeUniformSequence.run _ _ 930 258 NativePreparedKeyDecision.stops NativeAdaptedRecoverableCoupling.stops,
    PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).bind
    (fun c => NativeAdaptedRecoverableCoupling.kernelAt
      (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2)
        (NativePreparedState.state c)) = _
  change (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).bind
    (NativeAdaptedRecoverableCoupling.kernelAt
      (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2) ∘
        NativePreparedState.state) = _
  rw [← PMF.bind_map, NativePreparedState.framed_law]

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 1189).map
      NativePreparedState.state =
      ((tableEightBitLaw v message).map NativePreparedState.encode).bind
        (NativeAdaptedRecoverableCoupling.kernelAt
          (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativePreparedKeyDecision.entry_equivalent v message).symm 1189 _ NativePreparedState.state_equivalent]
  exact framed_law v message

theorem sharp_target_law (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1189).map
      NativePreparedState.state =
      (Roundtrip.q message).map (cleanEncode
        (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2)) := by
  rw [initial_law]
  change ((Roundtrip.p message).map NativePreparedState.encode).bind _ = _
  rw [← Recoverable.source_law message, PMF.map_comp, PMF.bind_map]
  simp only [Function.comp_def, source_kernel]
  rw [← PMF.map_bind]
  have h := congrArg (fun law : PMF (Fin 5 × Bool) => law.map (cleanEncode
    (NativePreparedKeyDecision.code.length + NativeAdaptedRecoverableCoupling.code.length + 2)))
      (Recoverable.target_law message)
  rw [PMF.map_comp] at h
  exact h

theorem stops : StopsEverywhere code 1189 :=
  NativeUniformSequence.stops NativePreparedKeyDecision.code NativeAdaptedRecoverableCoupling.code 930 258
    NativePreparedKeyDecision.stops NativeAdaptedRecoverableCoupling.stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 1189 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 1189
  polynomial := PolynomiallyBounded.const 1189
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end
end Machine.NativeReferenceCouplingExecution
