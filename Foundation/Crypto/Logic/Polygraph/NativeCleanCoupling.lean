import Foundation.Crypto.Logic.Polygraph.NativeCouplingSampler
import Foundation.Crypto.Semantics.Machine.NativeCleanRecoverableCoupling

/-! The history-erasing native program realizes the same finite repaired
kernel and public result as the earlier sampler. All erasure is charged in
the native 212-step contract. Logical bind contexts still receive no free
machine implementation or runtime contract. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCleanCoupling
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def nativeLaw (bit ciphertext : Bool) : PMF (Fin 5) :=
  (Machine.evalConfigWithin Machine.NativeCleanRecoverableCoupling.code
    (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext)) 212).map
      (NativeCouplingSampler.pick ∘ Machine.NativeRecoverableCouplingExecution.observe)

theorem native_law (bit ciphertext : Bool) : nativeLaw bit ciphertext = Recoverable.forward bit := by
  have h := congrArg (fun law => law.map NativeCouplingSampler.pick)
    (Machine.NativeCleanRecoverableCoupling.initial_law bit ciphertext)
  rw [PMF.map_comp, PMF.map_comp] at h
  change nativeLaw bit ciphertext = (Recoverable.forward bit).map id at h
  simpa only [PMF.map_id] using h

def nativeProgram (bit ciphertext : Bool) : Program (Fin 5) := .sample (nativeLaw bit ciphertext)

theorem native_realization (bit ciphertext : Bool) :
    (nativeProgram bit ciphertext).eval =
      (Machine.evalConfigWithin Machine.NativeCleanRecoverableCoupling.bounded.program
        (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext))
        (Machine.NativeCleanRecoverableCoupling.bounded.budget 2)).map
          (NativeCouplingSampler.pick ∘ Machine.NativeRecoverableCouplingExecution.observe) := rfl

def reification (bit ciphertext : Bool) :
    ExactStep (nativeProgram bit ciphertext) (NativeCouplingSampler.referenceProgram bit) :=
  .distribution (native_law bit ciphertext)

def contextPath {A : Type} (bit ciphertext : Bool) (next : Fin 5 → Program A) :
    ExactPath (.bind (nativeProgram bit ciphertext) next)
      (.bind (NativeCouplingSampler.referenceProgram bit) next) :=
  .step (.bindFirst (reification bit ciphertext) next)

def nativeResultLaw (bit ciphertext : Bool) : PMF (Option (Fin 5 × Bool)) :=
  (Machine.evalConfigWithin Machine.NativeCleanRecoverableCoupling.code
    (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext)) 212).map
      Machine.NativeRecoverableCouplingExecution.keyCiphertext

theorem native_result_law (bit ciphertext : Bool) :
    nativeResultLaw bit ciphertext = NativeCouplingSampler.nativeResultLaw bit ciphertext := by
  have h := congrArg (fun law => law.map Prod.fst)
    (Machine.NativeCleanRecoverableCoupling.initial_law bit ciphertext)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h.trans (NativeCouplingSampler.native_result_law bit ciphertext).symm

theorem native_result_target (message : Bool) :
    (Recoverable.sourceLaw.bind fun bit => nativeResultLaw bit (Recoverable.sourceResult message bit).2) =
      (Roundtrip.q message).map some := by
  simp_rw [native_result_law]
  exact NativeCouplingSampler.native_result_target message

theorem output_finish (pc : ℕ) (bit ciphertext : Bool) (key : Fin 5) (inputSuffix : Machine.Tape) :
    (Machine.NativeCleanRecoverableCoupling.finish pc bit ciphertext key inputSuffix {}).outputBits =
      [ciphertext,bit] := rfl

theorem public_packet (bit ciphertext : Bool) :
    Machine.evalWithin Machine.NativeCleanRecoverableCoupling.code
      (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext) 212 = PMF.pure (some [ciphertext,bit]) := by
  rw [Machine.NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 212
    (Machine.NativeCleanRecoverableCoupling.haltsWithin _)]
  rw [Machine.evalConfigWithin_map_eq_of_equivalent _ _ _
    (Machine.NativeRecoverableKeySampler.entry_equivalent bit ciphertext).symm 212 _ (by
      intro c d h
      exact congrArg some h.outputBits)]
  rw [Machine.NativeCleanRecoverableCoupling.full_run, PMF.map_comp]
  have h : (fun c : Machine.Configuration => some c.outputBits) ∘
      (fun key => Machine.NativeCleanRecoverableCoupling.finish
        (Machine.NativeRecoverableCouplingExecution.code.length + Machine.NativeCleanRecoverableCoupling.cleanup.length + 2)
        bit ciphertext key {} {}) = Function.const (Fin 5) (some [ciphertext,bit]) := by
    funext key
    rw [Function.comp_apply, output_finish]
    rfl
  rw [h, PMF.map_const]

end
end CryptoLogic.Polygraph.Experiment.NativeCleanCoupling
