import Foundation.Machine.FramedScalarInput
import Foundation.Machine.ScalarSamplePadding
import Foundation.Machine.SavedRejectionSamplingSemantics

namespace Machine.FramedScalarSampler

/-- One finite framed scalar sampler: prepare q and the width counter,
invoke the existing exact rejection code, and physically pad its accepted
result. The linked distribution and expected-time certificates must account
for the random subroutine's return as well as these deterministic stages. -/
def program : Program :=
  (FramedScalarInput.program.followedBy RejectionSampling.program).followedBy ScalarSamplePadding.program

/-- An accepted operational sampler branch continues on its actual tapes
through fixed-width padding. Source random transitions are all charged.
This branch certificate does not replace the linked program's probability
or expected-time theorem. -/
theorem runs_from_sample (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3))
    (sample : List Bool) (hSample : sample.length ≤ n+3)
    (accepted : Configuration) (sampleSteps : Nat)
    (sampleRun : RunsFor RejectionSampling.program
      (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits) accepted sampleSteps)
    (sampleHalt : accepted.halted = true)
    (sampleInput : accepted.inputTape.Equivalent
      { left := q.bits.reverse.map some ++ none::List.replicate (n+3) (some true) })
    (sampleOutput : accepted.outputTape.Equivalent { left := sample.reverse.map some }) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ FramedScalarInput.validBudget n modulus generator + sampleSteps + 13*(n+3)+19 ∧
      RunsFor program (Configuration.initial
        (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator))) target used ∧
      target.halted = true ∧ target.outputBits = Binary.encode (n+3) (Binary.value sample) := by
  obtain ⟨prepared, u, hu, prepRun, prepHalt, prepInput, prepOutput⟩ :=
    FramedScalarInput.runs_valid n modulus generator q hWidth hPositive hFit
  have samplerLayout :
      (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits).Equivalent
        (prepared.resumeAt 0) := ⟨rfl, rfl, prepInput.symm, prepOutput.symm⟩
  obtain ⟨actualSample, v, hv, linked₁, halt₁, input₁, output₁⟩ :=
    prepRun.followedBy_equivalent sampleRun samplerLayout (Nat.zero_le _) rfl prepHalt sampleHalt
  have actualInput := input₁.symm.trans sampleInput
  have actualOutput := output₁.symm.trans sampleOutput
  have hLength : q.bits.length ≤ n+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  obtain ⟨padded, z, hz, padRun, padHalt, padOutput⟩ := ScalarSamplePadding.runs (n+3) q.bits sample hLength hSample
  have padLayout :
      ({ inputTape := { left := q.bits.reverse.map some ++ none::List.replicate (n+3) (some true) }
         outputTape := { left := sample.reverse.map some } } : Configuration).Equivalent (actualSample.resumeAt 0) :=
    ⟨rfl, rfl, actualInput.symm, actualOutput.symm⟩
  obtain ⟨target, used, hUsed, run, hHalt, _, hOutput⟩ :=
    linked₁.followedBy_equivalent padRun padLayout (Nat.zero_le _) rfl halt₁ padHalt
  exact ⟨target, used, by omega, run, hHalt, hOutput.bits.symm.trans padOutput⟩

end Machine.FramedScalarSampler
