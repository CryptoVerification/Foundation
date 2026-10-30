import Foundation.Crypto.Semantics.Machine.NativeCouplingExitAdapter

/-! Canonical public packet and full-cell target law, with a genuinely
executed common terminal control position. A padded target reference program
has the same final control as the transformed experiment; its extra executed
steps are counted. No free program-counter normalization is asserted. -/
namespace Machine.NativeCanonicalCouplingExecution
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def code : Program := NativeReferenceCouplingExecution.code.followedBy NativeCouplingExitAdapter.code

def padding : Program := List.replicate
  (NativeAdaptedRecoverableCoupling.code.length + NativeCouplingExitAdapter.code.length + 2 + 1) .halt

def targetCode : Program := NativePreparedKeyDecision.code.followedBy padding

theorem halt_padding_stops (n : ℕ) : StopsEverywhere (List.replicate (n + 1) .halt) 1 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  simp [List.replicate_succ, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next] at h
  subst finish
  rfl

theorem padding_stops : StopsEverywhere padding 1 := halt_padding_stops _

theorem final_control_equal :
    NativeReferenceCouplingExecution.code.length + NativeCouplingExitAdapter.code.length + 2 =
      NativePreparedKeyDecision.code.length + padding.length + 2 := by
  rw [NativeReferenceCouplingExecution.code, NativeUniformSequence.code_length,
    padding, List.length_replicate]
  omega

theorem transformed_law (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1219).map
      NativePreparedState.state =
      (Roundtrip.q message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish
          (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  unfold code
  change (evalConfigWithin (NativeReferenceCouplingExecution.code.followedBy NativeCouplingExitAdapter.code)
    (NativeBitChoice.start (Tape.ofBits (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) {})
    (1189 + 29 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 1189 29 NativeReferenceCouplingExecution.stops NativeCouplingExitAdapter.stops,
    PMF.map_bind]
  simp only [PMF.map_comp]
  change (evalConfigWithin NativeReferenceCouplingExecution.code
    (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1189).bind
      (NativeCouplingExitAdapter.kernelAt
        (NativeReferenceCouplingExecution.code.length + NativeCouplingExitAdapter.code.length + 2) ∘
          NativePreparedState.state) = _
  rw [← PMF.bind_map, NativeReferenceCouplingExecution.sharp_target_law, PMF.bind_map]
  simp only [Function.comp_def, NativeCouplingExitAdapter.kernelAt_clean, final_control_equal]
  rfl

theorem target_framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin targetCode (NativePreparedKeyDecision.entry v message) 932).map NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  unfold targetCode NativePreparedKeyDecision.entry
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
      (NativePreparedKeyDecision.code.length + padding.length + 2))))
        (NativePreparedState.framed_law v message)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

theorem target_initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin targetCode (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 932).map
      NativePreparedState.state =
      (tableEightBitLaw v message).map (fun result => NativePreparedState.state
        (NativePreparedState.finish (NativePreparedKeyDecision.code.length + padding.length + 2) result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativePreparedKeyDecision.entry_equivalent v message).symm 932 _ NativePreparedState.state_equivalent]
  exact target_framed_law v message

theorem full_cell_law_equal (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)) 1219).map
      NativePreparedState.state =
    (evalConfigWithin targetCode
      (Configuration.initial (NativePreparedKeyDecision.rawInput (sharpTableChain 2) message)) 932).map
      NativePreparedState.state := by
  rw [transformed_law, target_initial_law]
  rfl

theorem stops : StopsEverywhere code 1219 :=
  NativeUniformSequence.stops NativeReferenceCouplingExecution.code NativeCouplingExitAdapter.code 1189 29
    NativeReferenceCouplingExecution.stops NativeCouplingExitAdapter.stops

theorem target_stops : StopsEverywhere targetCode 932 :=
  NativeUniformSequence.stops NativePreparedKeyDecision.code padding 930 1
    NativePreparedKeyDecision.stops padding_stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 1219 := stops (Tape.ofBits input) {}
theorem target_haltsWithin (input : List Bool) : HaltsWithin targetCode input 932 := target_stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 1219
  polynomial := PolynomiallyBounded.const 1219
  halts := haltsWithin

def targetBounded : CryptoLogic.BoundedProgram where
  program := targetCode
  budget := fun _ => 932
  polynomial := PolynomiallyBounded.const 932
  halts := target_haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime
theorem target_polynomial_time : PolynomialTime targetCode := targetBounded.polynomialTime

theorem padding_length : padding.length ≤ 8671 := by
  have ha := NativeAdaptedRecoverableCoupling.code_length
  have he := NativeCouplingExitAdapter.code_length
  rw [padding, List.length_replicate]
  omega

theorem code_length_equal : code.length = targetCode.length := by
  have h := final_control_equal
  rw [code, targetCode, NativeUniformSequence.code_length, NativeUniformSequence.code_length]
  omega

def outputView : NativePreparedState.State → Option (List Bool) :=
  Quotient.lift (fun c => some c.outputBits) (by
    intro c d h
    exact congrArg some h.outputBits)

theorem public_law_equal (message : Bool) :
    evalWithin code (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message) 1219 =
      evalWithin targetCode (NativePreparedKeyDecision.rawInput (sharpTableChain 2) message) 932 := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 1219 (haltsWithin _),
    NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 932 (target_haltsWithin _)]
  have h := congrArg (fun law => law.map outputView) (full_cell_law_equal message)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

theorem outputView_finish (pc : ℕ) (result : Fin 5 × Bool) :
    outputView (NativePreparedState.state (NativePreparedState.finish pc result)) =
      some [!result.2,keyPairTest result] := rfl

theorem outputView_encode (result : Fin 5 × Bool) :
    outputView (NativePreparedState.encode result) = some [!result.2,keyPairTest result] :=
  outputView_finish _ result

theorem target_public_reference (v : OrderedGridVertex 32) (message : Bool) :
    evalWithin targetCode (NativePreparedKeyDecision.rawInput v message) 932 =
      evalWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.rawInput v message) 930 := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 932 (target_haltsWithin _),
    NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 930 (NativePreparedKeyDecision.haltsWithin _)]
  have ht := congrArg (fun law => law.map outputView) (target_initial_law v message)
  have hs := congrArg (fun law => law.map outputView) (NativePreparedState.initial_law v message)
  rw [PMF.map_comp, PMF.map_comp] at ht hs
  simp only [Function.comp_def, outputView_finish, outputView_encode] at ht hs
  exact ht.trans hs.symm

theorem public_reference_law_equal (message : Bool) :
    evalWithin code (NativePreparedKeyDecision.rawInput (sharpTableChain 0) message) 1219 =
      evalWithin NativePreparedKeyDecision.code
        (NativePreparedKeyDecision.rawInput (sharpTableChain 2) message) 930 := by
  exact (public_law_equal message).trans (target_public_reference (sharpTableChain 2) message)

end
end Machine.NativeCanonicalCouplingExecution
