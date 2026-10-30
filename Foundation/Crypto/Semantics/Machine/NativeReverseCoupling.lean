import Foundation.Crypto.Semantics.Machine.NativeRecoveryWriter

/-! A native deterministic reverse uses the intermediate key only. It reads
the current reference packet, reconstructs source label 0 or 2, erases its
request, and restores the reference cell layout and public packet. -/
namespace Machine.NativeReverseCoupling
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def code : Program := NativeCouplingRequestAdapter.code.followedBy NativeRecoveryWriter.code

theorem prepared_equivalent (pc : ℕ) (bit ciphertext : Bool) :
    ((NativeCouplingRequestAdapter.prepared pc bit ciphertext).resumeAt 0).Equivalent
      (NativeRecoveryWriter.entry bit ciphertext) := by
  have hi : ((NativeCouplingRequestAdapter.prepared pc bit ciphertext).resumeAt 0).Equivalent
      (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) := by
    refine ⟨rfl,rfl,?_,NativeAdaptedRecoverableCoupling.blank_left 2⟩
    exact (NativeControlledCipherInitial.preload_equivalent _ (NativeAdaptedRecoverableCoupling.blank_left 30)).trans
      (NativeControlledCipherInitial.preload_empty _)
  have he := NativeRecoveryWriter.entry_equivalent bit ciphertext
  exact ⟨hi.1.trans he.1.symm,hi.2.1.trans he.2.1.symm,
    hi.2.2.1.trans he.2.2.1.symm,hi.2.2.2.trans he.2.2.2.symm⟩

theorem writer_kernel (pc oldPc : ℕ) (bit ciphertext : Bool) :
    (evalConfigWithin NativeRecoveryWriter.code
      ((NativeCouplingRequestAdapter.prepared oldPc bit ciphertext).resumeAt 0) 55).map
        (NativeAdaptedRecoverableCoupling.atControl pc) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc (NativeRecoveryWriter.result bit ciphertext))) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (prepared_equivalent oldPc bit ciphertext) 55 _
    (NativeAdaptedRecoverableCoupling.atControl_equivalent pc), NativeRecoveryWriter.run, PMF.pure_map]
  change PMF.pure (NativePreparedState.state (NativeRecoveryWriter.finish pc bit ciphertext)) = _
  rw [NativePreparedState.state_equivalent _ _ (NativeRecoveryWriter.finish_equivalent pc bit ciphertext)]

theorem run_at (pc oldPc : ℕ) (result : Fin 5 × Bool) :
    (evalConfigWithin code ((NativePreparedState.finish oldPc result).resumeAt 0) 101).map
      (NativeAdaptedRecoverableCoupling.atControl pc) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc
        (NativeRecoveryWriter.result (Recoverable.parent result.1) result.2))) := by
  unfold code
  change (evalConfigWithin (NativeCouplingRequestAdapter.code.followedBy NativeRecoveryWriter.code)
    (NativeBitChoice.start (NativePreparedState.finish oldPc result).inputTape
      (NativePreparedState.finish oldPc result).outputTape) (45 + 55 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 45 55 NativeCouplingRequestAdapter.stops NativeRecoveryWriter.stops]
  change ((evalConfigWithin NativeCouplingRequestAdapter.code
    ((NativePreparedState.finish oldPc result).resumeAt 0) 45).bind _).map _ = _
  rw [NativeCouplingRequestAdapter.run, PMF.pure_bind, PMF.map_comp]
  exact writer_kernel pc _ _ _

noncomputable def kernelAt (pc : ℕ) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin code (c.resumeAt 0) 101).map
    (NativeAdaptedRecoverableCoupling.atControl pc)) (by
      intro c d h
      exact evalConfigWithin_map_eq_of_equivalent _ _ _
        (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 101 _
          (NativeAdaptedRecoverableCoupling.atControl_equivalent pc))

theorem reconstruct_target (message : Bool) (key : Fin 5) :
    NativeRecoveryWriter.result (Recoverable.parent key) (Recoverable.targetResult message key).2 =
      Recoverable.sourceResult message (Recoverable.parent key) := by
  cases h : Recoverable.parent key <;>
    simp [NativeRecoveryWriter.result, NativeRecoveryWriter.sourceKey, Recoverable.sourceResult,
      Recoverable.targetResult, h]

theorem kernelAt_target (pc oldPc : ℕ) (message : Bool) (key : Fin 5) :
    kernelAt pc (NativePreparedState.state (NativePreparedState.finish oldPc (Recoverable.targetResult message key))) =
      PMF.pure (NativePreparedState.state
        (NativePreparedState.finish pc (Recoverable.sourceResult message (Recoverable.parent key)))) := by
  change (evalConfigWithin code
    ((NativePreparedState.finish oldPc (Recoverable.targetResult message key)).resumeAt 0) 101).map _ = _
  rw [run_at]
  change PMF.pure (NativePreparedState.state (NativePreparedState.finish pc
    (NativeRecoveryWriter.result (Recoverable.parent key) (Recoverable.targetResult message key).2))) = _
  rw [reconstruct_target]

theorem stops : StopsEverywhere code 101 :=
  NativeUniformSequence.stops NativeCouplingRequestAdapter.code NativeRecoveryWriter.code 45 55
    NativeCouplingRequestAdapter.stops NativeRecoveryWriter.stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 101 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 101
  polynomial := PolynomiallyBounded.const 101
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem code_length : code.length ≤ 390 := by
  have ha := NativeCouplingRequestAdapter.code_length
  have hw := NativeRecoveryWriter.code_length
  rw [code, NativeUniformSequence.code_length]
  omega

end Machine.NativeReverseCoupling
