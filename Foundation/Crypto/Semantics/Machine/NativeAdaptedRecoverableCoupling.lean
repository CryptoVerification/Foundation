import Foundation.Crypto.Semantics.Machine.NativeCouplingRequestAdapter

/-! The reference full-cell exit is a native entry, not a free host request
conversion. The 45-step adapter and 212-step cleaned sampler run consecutively.
The resulting clean exit is still a different layout from the reference exit. -/
namespace Machine.NativeAdaptedRecoverableCoupling
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

theorem blank_left (n : ℕ) : ({left := List.replicate n none} : Tape).Equivalent {} := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  change (List.replicate n (none : Option Bool)).getD i none = none
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp [List.replicate_succ]
    | succ i => simpa only [List.replicate_succ, List.getD_cons_succ] using ih i

theorem prepared_equivalent (pc : ℕ) (bit ciphertext : Bool) :
    ((NativeCouplingRequestAdapter.prepared pc bit ciphertext).resumeAt 0).Equivalent
      (NativeRecoverableKeySampler.entry bit ciphertext {} {}) := by
  have hi : ((NativeCouplingRequestAdapter.prepared pc bit ciphertext).resumeAt 0).Equivalent
      (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) := by
    refine ⟨rfl, rfl, ?_, blank_left 2⟩
    exact (NativeControlledCipherInitial.preload_equivalent _ (blank_left 30)).trans
      (NativeControlledCipherInitial.preload_empty _)
  have he := NativeRecoverableKeySampler.entry_equivalent bit ciphertext
  exact ⟨hi.1.trans he.1.symm, hi.2.1.trans he.2.1.symm,
    hi.2.2.1.trans he.2.2.1.symm, hi.2.2.2.trans he.2.2.2.symm⟩

def code : Program := NativeCouplingRequestAdapter.code.followedBy NativeCleanRecoverableCoupling.code

def atControl (pc : ℕ) (c : Configuration) : NativePreparedState.State :=
  NativePreparedState.state {c with pc := pc, halted := true}

theorem atControl_equivalent (pc : ℕ) (c d : Configuration) (h : c.Equivalent d) :
    atControl pc c = atControl pc d :=
  NativePreparedState.state_equivalent _ _ ⟨rfl,rfl,h.2.2⟩

theorem clean_kernel (pc oldPc : ℕ) (bit ciphertext : Bool) :
    (evalConfigWithin NativeCleanRecoverableCoupling.code
      ((NativeCouplingRequestAdapter.prepared oldPc bit ciphertext).resumeAt 0) 212).map (atControl pc) =
      (Recoverable.forward bit).map (fun key => NativePreparedState.state
        (NativeCleanRecoverableCoupling.finish pc bit ciphertext key {} {})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (prepared_equivalent oldPc bit ciphertext)
    212 _ (atControl_equivalent pc), NativeCleanRecoverableCoupling.full_run, PMF.map_comp]
  rfl

theorem run_at (pc oldPc : ℕ) (result : Fin 5 × Bool) :
    (evalConfigWithin code ((NativePreparedState.finish oldPc result).resumeAt 0) 258).map (atControl pc) =
      (Recoverable.forward (Recoverable.parent result.1)).map (fun key => NativePreparedState.state
        (NativeCleanRecoverableCoupling.finish pc (Recoverable.parent result.1) result.2 key {} {})) := by
  unfold code
  change (evalConfigWithin (NativeCouplingRequestAdapter.code.followedBy NativeCleanRecoverableCoupling.code)
    (NativeBitChoice.start (NativePreparedState.finish oldPc result).inputTape
      (NativePreparedState.finish oldPc result).outputTape) (45 + 212 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 45 212 NativeCouplingRequestAdapter.stops NativeCleanRecoverableCoupling.stops]
  change ((evalConfigWithin NativeCouplingRequestAdapter.code
    ((NativePreparedState.finish oldPc result).resumeAt 0) 45).bind _).map _ = _
  rw [NativeCouplingRequestAdapter.run, PMF.pure_bind, PMF.map_comp]
  exact clean_kernel pc _ (Recoverable.parent result.1) result.2

noncomputable def kernelAt (pc : ℕ) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin code (c.resumeAt 0) 258).map (atControl pc)) (by
    intro c d h
    exact evalConfigWithin_map_eq_of_equivalent _ _ _ (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 258 _ (atControl_equivalent pc))

theorem kernelAt_finish (pc oldPc : ℕ) (result : Fin 5 × Bool) :
    kernelAt pc (NativePreparedState.state (NativePreparedState.finish oldPc result)) =
      (Recoverable.forward (Recoverable.parent result.1)).map (fun key => NativePreparedState.state
        (NativeCleanRecoverableCoupling.finish pc (Recoverable.parent result.1) result.2 key {} {})) :=
  run_at pc oldPc result

theorem stops : StopsEverywhere code 258 :=
  NativeUniformSequence.stops NativeCouplingRequestAdapter.code NativeCleanRecoverableCoupling.code 45 212
    NativeCouplingRequestAdapter.stops NativeCleanRecoverableCoupling.stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 258 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 258
  polynomial := PolynomiallyBounded.const 258
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem code_length : code.length ≤ 8519 := by
  have ha := NativeCouplingRequestAdapter.code_length
  have hs := NativeCleanRecoverableCoupling.code_length
  rw [code, NativeUniformSequence.code_length]
  omega

end Machine.NativeAdaptedRecoverableCoupling
