import Foundation.Crypto.Semantics.Machine.SavedFramedScalarInput
import Foundation.Crypto.Semantics.Machine.SavedScalarSamplerContinuation

namespace Machine.SavedFramedScalarSampler

/-- A framed native scalar sampler retaining the public request for later
key-generation/encryption arithmetic. The retained request is real tape data. -/
def program : Program := SavedFramedScalarInput.program.followedBy ScalarSamplerContinuation.program

theorem runs_from_sample_layout (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3))
    (sample : List Bool) (hSample : sample.length ≤ n+3)
    (accepted : Configuration) (sampleSteps : Nat)
    (sampleRun : RunsFor RejectionSampling.program
      (RejectionSampling.Saved.initial
        (List.replicate (n+3) (some true) ++ none::
          (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)).reverse.map some)
        q.bits) accepted sampleSteps)
    (sampleHalt : accepted.halted = true)
    (sampleInput : accepted.inputTape.Equivalent
      {left := q.bits.reverse.map some ++ none::(List.replicate (n+3) (some true) ++ none::
        (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)).reverse.map some)})
    (sampleOutput : accepted.outputTape.Equivalent {left := sample.reverse.map some}) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)
    ∃ target used, used ≤ SavedFramedScalarInput.validBudget n modulus generator + sampleSteps + 13*(n+3)+19 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some} ∧
      target.outputBits = Binary.encode (n+3) (Binary.value sample) ∧
      target.outputTape.Equivalent {left := (Binary.encode (n+3) (Binary.value sample)).reverse.map some} := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)
  obtain ⟨prepared, u, hu, prepRun, prepHalt, prepInput, prepOutput⟩ :=
    SavedFramedScalarInput.runs_valid n modulus generator q hWidth hPositive hFit
  have qLength : q.bits.length ≤ n+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  obtain ⟨padded, v, hv, sampleCode, halt, retained, bits, scalarLayout⟩ :=
    ScalarSamplerContinuation.runs_from_sample_saved_layout (raw.reverse.map some) (n+3) q.bits sample
      qLength hSample accepted sampleSteps sampleRun sampleHalt sampleInput sampleOutput
  have layout :
      (RejectionSampling.Saved.initial
        (List.replicate (n+3) (some true) ++ none::raw.reverse.map some) q.bits).Equivalent
          (prepared.resumeAt 0) := ⟨rfl, rfl, prepInput.symm, prepOutput.symm⟩
  obtain ⟨target, used, hUsed, run, hHalt, input, output⟩ :=
    prepRun.followedBy_equivalent sampleCode layout (Nat.zero_le _) rfl prepHalt halt
  exact ⟨target, used, by omega, run, hHalt, input.symm.trans retained, output.bits.symm.trans bits, output.symm.trans scalarLayout⟩

theorem runs_from_sample (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3))
    (sample : List Bool) (hSample : sample.length ≤ n+3)
    (accepted : Configuration) (sampleSteps : Nat)
    (sampleRun : RunsFor RejectionSampling.program
      (RejectionSampling.Saved.initial
        (List.replicate (n+3) (some true) ++ none::
          (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)).reverse.map some)
        q.bits) accepted sampleSteps)
    (sampleHalt : accepted.halted = true)
    (sampleInput : accepted.inputTape.Equivalent
      {left := q.bits.reverse.map some ++ none::(List.replicate (n+3) (some true) ++ none::
        (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)).reverse.map some)})
    (sampleOutput : accepted.outputTape.Equivalent {left := sample.reverse.map some}) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)
    ∃ target used, used ≤ SavedFramedScalarInput.validBudget n modulus generator + sampleSteps + 13*(n+3)+19 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some} ∧
      target.outputBits = Binary.encode (n+3) (Binary.value sample) := by
  dsimp only
  obtain ⟨target, used, bound, run, halted, input, bits, _⟩ :=
    runs_from_sample_layout n modulus generator q hWidth hPositive hFit sample hSample accepted sampleSteps
      sampleRun sampleHalt sampleInput sampleOutput
  exact ⟨target, used, bound, run, halted, input, bits⟩

end Machine.SavedFramedScalarSampler
