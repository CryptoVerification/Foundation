import Foundation.Crypto.Semantics.Machine.NativeEncryptionSample
import Foundation.Crypto.Semantics.Machine.SavedFramedScalarInput
import Foundation.Crypto.Semantics.Machine.NativeSequenceControl
import Foundation.Crypto.Semantics.Machine.NativeFinalHalt
import Foundation.Crypto.Semantics.Machine.SavedScalarSamplerContinuationDistribution
import Foundation.Crypto.Semantics.Machine.LimitExecution

namespace Machine.NativeEncryption

open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private theorem first_layout (first second : Program) :
    first.followedBy second = Program.withSubroutine [] first
      (second.asSubroutine (first.length+1) (first.length+second.length+2) ++ [.halt])
        (first.length+1) := by
  simp only [Program.followedBy, Program.withSubroutine, List.length_nil,
    Nat.zero_add, List.nil_append, List.append_assoc]

private theorem second_layout (first second : Program) :
    first.followedBy second = Program.withSubroutine
      (first.asSubroutine 0 (first.length+1)) second [.halt]
      ((first.asSubroutine 0 (first.length+1)).length+second.length+1) := by
  simp [Program.followedBy, Program.withSubroutine, List.append_assoc,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem linked_length (first second : Program) :
    (first.followedBy second).length = first.length+second.length+3 := by
  simp [Program.followedBy]; omega

def program : Program := SavedFramedScalarInput.program.followedBy NativeEncryptionSample.program

def request (n modulus generator q publicKey message : Nat) : List Bool :=
  encodeSecurityParameter n ++ frame (Binary.encode (n+3) modulus ++
    Binary.encode (n+3) q ++ Binary.encode (n+3) generator ++
    Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message)

private noncomputable def ideal (n modulus q generator publicKey message : Nat) [NeZero q] : PMF (List Bool) :=
  (Foundation.Probability.uniform (Fin q)).map (fun a =>
    frame (Binary.encode (n+3) (generator^a.val % modulus)) ++ frame (Binary.encode (n+3) (message*(publicKey^a.val % modulus) % modulus)))

/-- The deterministic framed prefix hands its actual retained tapes to the
random sampler. Every finite source output probability is present after
the prefix and one charged outer halt; timeout probability cannot increase.
The prefix count is one actual trace count, independent of retry branches. -/
theorem finite_law_from_frame (n : Nat) (modulus generator publicKey message : Nat) (q : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) (hMessage : message < modulus) (hPositive : q ≠ 0) (hFit : q < 2^(n+3)) :
    ∃ used : Nat, used ≤ SavedFramedScalarInput.validBudget n (Binary.encode (n+3) modulus) (Binary.encode (n+3) generator ++ Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message) ∧
      ∀ steps : Nat,
        timeoutProbabilityFrom program (Configuration.initial (request n modulus generator q publicKey message))
            (used+steps+1) ≤
          timeoutProbabilityFrom NativeEncryptionSample.program
            (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::(request n modulus generator q publicKey message).reverse.map some) q.bits) steps ∧
        ∀ bits : List Bool,
          ((evalConfigWithin NativeEncryptionSample.program
            (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::(request n modulus generator q publicKey message).reverse.map some) q.bits) steps).map
              report) (some bits) ≤
          ((evalConfigWithin program (Configuration.initial (request n modulus generator q publicKey message))
            (used+steps+1)).map report) (some bits) := by
  obtain ⟨prepared, used, hUsed, run, halted, input, output⟩ :=
    SavedFramedScalarInput.runs_valid n (Binary.encode (n+3) modulus) (Binary.encode (n+3) generator ++ Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message) q (by simp) hPositive hFit
  let first := SavedFramedScalarInput.program
  let core := NativeEncryptionSample.program
  let entry := first.length+1
  let pre := first.asSubroutine 0 entry
  let ret := pre.length+core.length+1
  let canonical := RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::(request n modulus generator q publicKey message).reverse.map some) q.bits
  have firstLayout : program = Program.withSubroutine [] first
      (core.asSubroutine entry ret ++ [.halt]) entry := by
    have h := first_layout first core
    have returnEq : first.length+core.length+2 = ret := by
      simp only [ret, pre, Program.asSubroutine_length, entry]
      omega
    rw [returnEq] at h
    exact h
  have coreLayout : program = Program.withSubroutine pre core [.halt] ret :=
    second_layout first core
  have firstClosed := Program.followedBy_control_closed
    ((((FramedExponentPreparation.program.followedBy GuardedCompiler.seekScratchInput).followedBy
      OutputColumnRewind.secondBoundaryToFirst).followedBy ScalarModulusPreparation.program.swapTapes).followedBy
        eraseOutputBlock) rewindBitstring
  have firstPc : (Configuration.initial (request n modulus generator q publicKey message)).pc < first.length := by
    change 0 < SavedFramedScalarInput.program.length
    unfold SavedFramedScalarInput.program
    rw [linked_length]
    omega
  have prefixCall := run.evalConfigWithin_withSubroutine_halted_of_closed [] first
    (core.asSubroutine entry ret ++ [.halt]) entry firstPc rfl halted firstClosed
      SavedFramedScalarInput.no_randomBit
  have prefixEval : evalConfigWithin program
      (Configuration.initial (request n modulus generator q publicKey message)) used =
      PMF.pure (prepared.resumeAt entry) := by
    simpa only [← firstLayout, List.length_nil, Configuration.rebasePc, Nat.zero_add, Configuration.initial, request, List.append_assoc] using prefixCall
  have equivalent : (canonical.rebasePc pre.length).Equivalent (prepared.resumeAt entry) := by
    refine ⟨?_, rfl, ?_, output.symm⟩
    · simp [canonical, RejectionSampling.Saved.initial, Configuration.rebasePc,
        Configuration.resumeAt, pre, entry]
    · simpa only [canonical, RejectionSampling.Saved.initial, Configuration.rebasePc,
        Configuration.resumeAt, request, List.append_assoc] using input.symm
  have closed := Program.followedBy_control_closed RejectionSampling.program NativeEncryptionSample.tail
  have corePc : canonical.pc < core.length := by
    change 0 < (RejectionSampling.program.followedBy NativeEncryptionSample.tail).length
    rw [linked_length]
    omega
  refine ⟨used, hUsed, ?_⟩
  intro steps
  have observed : (evalConfigWithin program
      (Configuration.initial (request n modulus generator q publicKey message)) (used+steps+1)).map report =
      (evalConfigWithin program (canonical.rebasePc pre.length) (steps+1)).map report := by
    rw [show used+steps+1 = used+(steps+1) by omega,
      evalConfigWithin_add, prefixEval, PMF.pure_bind]
    exact (equivalent.evalOutput program (steps+1)).symm
  constructor
  · change ((evalConfigWithin program _ (used+steps+1)).map report) none ≤ _
    rw [observed, coreLayout]
    exact Program.timeout_after_closed_call_le pre core canonical corePc rfl closed steps
  · intro bits
    rw [observed, coreLayout]
    exact Program.output_after_closed_call_le pre core canonical corePc rfl closed steps bits

/-- Exact eventual output law of the whole framed native program. Preparation,
random retries, physical fixed-width padding and the caller halt all execute
on the actual tapes; timeout mass is never conditionally renormalized. -/
theorem outputMass_from_frame (n : Nat) (modulus generator publicKey message : Nat) (q : Nat)
    [NeZero q] (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) (hMessage : message < modulus) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3))
    (bits : List Bool) :
    outputMassFrom program (Configuration.initial (request n modulus generator q publicKey message)) bits =
      ideal n modulus q generator publicKey message bits := by
  obtain ⟨used, _, finite⟩ := finite_law_from_frame n modulus generator publicKey message q hOne hModulus hGenerator hKey hMessage (by omega) hFit
  apply outputMassFrom_eq_of_dominates
  intro output
  unfold ideal
  rw [← NativeEncryptionSample.outputMass_nat n modulus q generator publicKey message hOne hModulus hTwo hFit hGenerator hKey hMessage output]
  unfold outputMassFrom
  apply iSup_le
  intro steps
  exact ((finite steps).2 output).trans (le_iSup (fun k =>
    ((evalConfigWithin program (Configuration.initial (request n modulus generator q publicKey message)) k).map
      report) (some output)) (used+steps+1))

/-- The entire framed sampler has polynomial expected native transition
cost: deterministic preparation plus a polynomial arithmetic and sampling allowance.
Unbounded rejection branches remain present in its operational semantics. -/
theorem expectedSteps_from_frame (n : Nat) (modulus generator publicKey message : Nat) (q : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) (hMessage : message < modulus) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    expectedSteps program (request n modulus generator q publicKey message) ≤
      ((SavedFramedScalarInput.validBudget n (Binary.encode (n+3) modulus) (Binary.encode (n+3) generator ++ Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message) + 1 + NativeEncryptionSample.expectedBudget n : Nat) : ℝ≥0∞) := by
  obtain ⟨used, hUsed, finite⟩ := finite_law_from_frame n modulus generator publicKey message q hOne hModulus hGenerator hKey hMessage (by omega) hFit
  rw [← expectedStepsFrom_initial]
  have tailBound : (∑' steps : Nat, timeoutProbabilityFrom program
      (Configuration.initial (request n modulus generator q publicKey message)) (steps+(used+1))) ≤
      expectedStepsFrom NativeEncryptionSample.program
        (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::(request n modulus generator q publicKey message).reverse.map some) q.bits) := by
    apply ENNReal.tsum_le_tsum
    intro steps
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (finite steps).1
  have splitBound : expectedStepsFrom program (Configuration.initial (request n modulus generator q publicKey message)) ≤
      ((used+1 : Nat) : ℝ≥0∞) + expectedStepsFrom NativeEncryptionSample.program
        (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::(request n modulus generator q publicKey message).reverse.map some) q.bits) := by
    unfold expectedStepsFrom
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := used+1)]
    apply add_le_add _ tailBound
    calc
      _ ≤ ∑ _steps ∈ Finset.range (used+1), (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun steps _ => PMF.coe_le_one _ _)
      _ = _ := by simp
  calc
    _ ≤ ((used+1 : Nat) : ℝ≥0∞) + ((NativeEncryptionSample.expectedBudget n : Nat) : ℝ≥0∞) :=
      splitBound.trans (add_le_add le_rfl
        (NativeEncryptionSample.expectedSteps_nat n modulus q generator publicKey message hOne hModulus hTwo hFit hGenerator hKey hMessage))
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr (Nat.add_le_add_right (Nat.add_le_add_right hUsed 1)
        (NativeEncryptionSample.expectedBudget n))

theorem almostSureHalts_from_frame (n : Nat) (modulus generator publicKey message : Nat) (q : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) (hMessage : message < modulus) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    AlmostSureHalts program (request n modulus generator q publicKey message) := by
  apply almostSureHalts_of_expectedSteps_ne_top
  exact ne_of_lt ((expectedSteps_from_frame n modulus generator publicKey message q hOne hModulus hGenerator hKey hMessage hTwo hFit).trans_lt
    (ENNReal.natCast_lt_top _))

/-- The probability-one stopping certificate exposes the ordinary unbounded
machine evaluator directly as the exact ciphertext PMF. -/
theorem evalLimit_from_frame (n : Nat) (modulus generator publicKey message : Nat) (q : Nat)
    [NeZero q] (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) (hMessage : message < modulus) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    evalLimit program (request n modulus generator q publicKey message)
      (almostSureHalts_from_frame n modulus generator publicKey message q hOne hModulus hGenerator hKey hMessage hTwo hFit) =
      ideal n modulus q generator publicKey message := by
  apply PMF.ext
  intro bits
  exact outputMass_from_frame n modulus generator publicKey message q hOne hModulus hGenerator hKey hMessage hTwo hFit bits

/-- A single explicit polynomial covers framing, exact rejection sampling,
both powers, multiplication, scratch erasure and ciphertext output. -/
theorem expectedBudget_polynomiallyBounded (modulus generator publicKey message : Nat → Nat) :
    PolynomiallyBounded (fun n => SavedFramedScalarInput.validBudget n
      (Binary.encode (n+3) (modulus n))
      (Binary.encode (n+3) (generator n) ++ Binary.encode (n+3) (publicKey n) ++ Binary.encode (n+3) (message n)) + 1 +
        NativeEncryptionSample.expectedBudget n) := by
  have prep : PolynomiallyBounded (fun n => SavedFramedScalarInput.validBudget n
      (Binary.encode (n+3) (modulus n))
      (Binary.encode (n+3) (generator n) ++ Binary.encode (n+3) (publicKey n) ++ Binary.encode (n+3) (message n))) := by
    apply ((PolynomiallyBounded.const 10000).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).mono
    intro n
    simp only [SavedFramedScalarInput.validBudget,FramedExponentPreparation.validBudget,
      List.length_append,Binary.encode_length,BinaryThirdColumnTemplate.columns_length]
    omega
  exact (prep.add (PolynomiallyBounded.const 1)).add NativeEncryptionSample.expectedBudget_polynomiallyBounded

end Machine.NativeEncryption
