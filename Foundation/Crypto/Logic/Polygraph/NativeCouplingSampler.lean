import Foundation.Crypto.Logic.Polygraph.NativeCouplingRepair
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation
import Foundation.Crypto.Semantics.Machine.NativeRecoverableCouplingExecution

/-! The bounded native sampler/recovery caller realizes the repaired finite
key kernel. Canonical state reconstruction is a semantic view; a native
adapter from full reference configurations to the two-bit request is not
provided here. Logical continuations receive no free native runtime. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCouplingSampler
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def pick (result : Option (Fin 5 × Bool) × Option Bool) : Fin 5 := (result.1.map Prod.fst).getD 0

def nativeLaw (bit ciphertext : Bool) : PMF (Fin 5) :=
  (Machine.evalConfigWithin Machine.NativeRecoverableCouplingExecution.code
    (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext)) 111).map
      (pick ∘ Machine.NativeRecoverableCouplingExecution.observe)

theorem native_law (bit ciphertext : Bool) : nativeLaw bit ciphertext = Recoverable.forward bit := by
  have h := congrArg (fun law => law.map pick) (Machine.NativeRecoverableCouplingExecution.initial_law bit ciphertext)
  rw [PMF.map_comp, PMF.map_comp] at h
  change nativeLaw bit ciphertext = (Recoverable.forward bit).map id at h
  simpa only [PMF.map_id] using h

def nativeProgram (bit ciphertext : Bool) : Program (Fin 5) := .sample (nativeLaw bit ciphertext)
def referenceProgram (bit : Bool) : Program (Fin 5) := .sample (Recoverable.forward bit)

theorem native_realization (bit ciphertext : Bool) :
    (nativeProgram bit ciphertext).eval =
      (Machine.evalConfigWithin Machine.NativeRecoverableCouplingExecution.bounded.program
        (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext))
        (Machine.NativeRecoverableCouplingExecution.bounded.budget 2)).map (pick ∘ Machine.NativeRecoverableCouplingExecution.observe) := rfl

def reification (bit ciphertext : Bool) : ExactStep (nativeProgram bit ciphertext) (referenceProgram bit) :=
  .distribution (native_law bit ciphertext)

def contextPath {A : Type} (bit ciphertext : Bool) (next : Fin 5 → Program A) :
    ExactPath (.bind (nativeProgram bit ciphertext) next) (.bind (referenceProgram bit) next) :=
  .step (.bindFirst (reification bit ciphertext) next)

def nativeForward (message bit : Bool) : PMF (Fin 5) :=
  nativeLaw bit (Recoverable.sourceResult message bit).2

theorem nativeForward_eq (message : Bool) : nativeForward message = Recoverable.forward := by
  funext bit
  exact native_law bit _

theorem native_recovers (message bit : Bool) :
    (nativeForward message bit).map Recoverable.parent = PMF.pure bit := by
  rw [nativeForward_eq]
  exact Recoverable.recovers bit

theorem native_target_marginal (message : Bool) :
    (Recoverable.sourceLaw.bind (nativeForward message)).map (NativeRecoverable.targetView message) =
      NativeState.nativeLaw (sharpTableChain 2) message := by
  rw [nativeForward_eq]
  exact NativeRecoverable.target_native_law message


def nativeResultLaw (bit ciphertext : Bool) : PMF (Option (Fin 5 × Bool)) :=
  (Machine.evalConfigWithin Machine.NativeRecoverableCouplingExecution.code
    (Machine.Configuration.initial (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext)) 111).map
      Machine.NativeRecoverableCouplingExecution.keyCiphertext

theorem native_result_law (bit ciphertext : Bool) :
    nativeResultLaw bit ciphertext = (Recoverable.forward bit).map (fun key => some (key,ciphertext)) := by
  have h := congrArg (fun law => law.map Prod.fst) (Machine.NativeRecoverableCouplingExecution.initial_law bit ciphertext)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

theorem native_result_target (message : Bool) :
    (Recoverable.sourceLaw.bind fun bit => nativeResultLaw bit (Recoverable.sourceResult message bit).2) =
      (Roundtrip.q message).map some := by
  have row (bit : Bool) : nativeResultLaw bit (Recoverable.sourceResult message bit).2 =
      (Recoverable.forward bit).map (fun key => some (Recoverable.targetResult message key)) := by
    rw [native_result_law]
    change (Recoverable.forward bit).bind (fun key => PMF.pure (some (key,(Recoverable.sourceResult message bit).2))) =
      (Recoverable.forward bit).bind (fun key => PMF.pure (some (Recoverable.targetResult message key)))
    apply bind_congr_of_support
    intro key supported
    have parent := Recoverable.parent_supported bit key supported
    cases bit <;> simp [Recoverable.sourceResult, Recoverable.targetResult, parent]
  simp_rw [row]
  rw [← PMF.map_bind]
  have h := congrArg (fun law : PMF (Fin 5 × Bool) => law.map some) (Recoverable.target_law message)
  rw [PMF.map_comp] at h
  exact h

theorem output_finish (bit ciphertext : Bool) (inputSuffix : Machine.Tape) (coins : Fin 7 → Bool) :
    (Machine.NativeRecoverableCouplingExecution.finish bit ciphertext inputSuffix {} coins).outputBits = [ciphertext,bit] := rfl

theorem public_packet (bit ciphertext : Bool) :
    Machine.evalWithin Machine.NativeRecoverableCouplingExecution.code
      (Machine.NativeRecoverableKeySampler.rawInput bit ciphertext) 111 = PMF.pure (some [ciphertext,bit]) := by
  rw [Machine.NativeKeyPairOutputPacket.evalWithin_of_halts _ _ 111
    (Machine.NativeRecoverableCouplingExecution.haltsWithin _)]
  rw [Machine.evalConfigWithin_map_eq_of_equivalent _ _ _
    (Machine.NativeRecoverableKeySampler.entry_equivalent bit ciphertext).symm 111 _ (by
      intro c d h
      exact congrArg some h.outputBits)]
  rw [Machine.NativeRecoverableCouplingExecution.full_run, PMF.map_comp]
  have h : (fun c : Machine.Configuration => some c.outputBits) ∘
      Machine.NativeRecoverableCouplingExecution.finish bit ciphertext {} {} =
        Function.const (Fin 7 → Bool) (some [ciphertext,bit]) := by
    funext coins
    rw [Function.comp_apply, output_finish]
    rfl
  rw [h, PMF.map_const]

end
end CryptoLogic.Polygraph.Experiment.NativeCouplingSampler
