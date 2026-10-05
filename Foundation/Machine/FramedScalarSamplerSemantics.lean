import Foundation.Machine.FramedScalarSampler
import Foundation.Machine.NativeSequenceControl
import Foundation.Machine.NativeFinalHalt
import Foundation.Machine.ScalarSamplerContinuationDistribution
import Foundation.Machine.LimitExecution

namespace Machine.FramedScalarSampler

open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private def request (n : Nat) (modulus generator : List Bool) (q : Nat) : List Bool :=
  encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)

/-- The deterministic framed prefix hands its actual retained tapes to the
random sampler. Every finite source output probability is present after
the prefix and one charged outer halt; timeout probability cannot increase.
The prefix count is one actual trace count, independent of retry branches. -/
theorem finite_law_from_frame (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3)) :
    ∃ used : Nat, used ≤ FramedScalarInput.validBudget n modulus generator ∧
      ∀ steps : Nat,
        timeoutProbabilityFrom program (Configuration.initial (request n modulus generator q))
            (used+steps+1) ≤
          timeoutProbabilityFrom ScalarSamplerContinuation.program
            (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits) steps ∧
        ∀ bits : List Bool,
          ((evalConfigWithin ScalarSamplerContinuation.program
            (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits) steps).map
              report) (some bits) ≤
          ((evalConfigWithin program (Configuration.initial (request n modulus generator q))
            (used+steps+1)).map report) (some bits) := by
  obtain ⟨prepared, used, hUsed, run, halted, input, output⟩ :=
    FramedScalarInput.runs_valid n modulus generator q hWidth hPositive hFit
  let first := FramedScalarInput.program
  let core := ScalarSamplerContinuation.program
  let entry := first.length+1
  let pre := first.asSubroutine 0 entry
  let ret := pre.length+core.length+1
  let canonical := RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits
  have firstLayout : program = Program.withSubroutine [] first
      (core.asSubroutine entry ret ++ [.halt]) entry := by
    simp [program, Program.followedBy, Program.withSubroutine, pre, ret, entry, first, core, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have coreLayout : program = Program.withSubroutine pre core [.halt] ret := by
    simp [program, Program.followedBy, Program.withSubroutine, pre, ret, entry, first, core,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have firstClosed := Program.followedBy_control_closed
    FramedScalarPreparation.program rewindBitstring
  have firstPc : (Configuration.initial (request n modulus generator q)).pc < first.length := by
    simp [first, FramedScalarInput.program, Program.followedBy, Configuration.initial]
  have prefixCall := run.evalConfigWithin_withSubroutine_halted_of_closed [] first
    (core.asSubroutine entry ret ++ [.halt]) entry firstPc rfl halted firstClosed
      FramedScalarInput.no_randomBit
  have prefixEval : evalConfigWithin program
      (Configuration.initial (request n modulus generator q)) used =
      PMF.pure (prepared.resumeAt entry) := by
    simpa only [← firstLayout, List.length_nil, Configuration.rebasePc, Nat.zero_add, Configuration.initial, request] using prefixCall
  have equivalent : (canonical.rebasePc pre.length).Equivalent (prepared.resumeAt entry) := by
    refine ⟨?_, rfl, input.symm, output.symm⟩
    simp [canonical, RejectionSampling.Saved.initial, Configuration.rebasePc,
      Configuration.resumeAt, pre, entry]
  have closed := Program.followedBy_control_closed RejectionSampling.program ScalarSamplePadding.program
  have corePc : canonical.pc < core.length := by
    simp [canonical, RejectionSampling.Saved.initial, core, ScalarSamplerContinuation.program,
      Program.followedBy]
  refine ⟨used, hUsed, ?_⟩
  intro steps
  have observed : (evalConfigWithin program
      (Configuration.initial (request n modulus generator q)) (used+steps+1)).map report =
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
theorem outputMass_from_frame (n : Nat) (modulus generator : List Bool) (q : Nat)
    [NeZero q] (hWidth : modulus.length = n+3) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3))
    (bits : List Bool) :
    outputMassFrom program (Configuration.initial (request n modulus generator q)) bits =
      ((Foundation.Probability.uniform (Fin q)).map (fun a => Binary.encode (n+3) a.val)) bits := by
  obtain ⟨used, _, finite⟩ := finite_law_from_frame n modulus generator q hWidth (by omega) hFit
  apply outputMassFrom_eq_of_dominates
  intro output
  rw [← ScalarSamplerContinuation.outputMass_nat (n+3) q hTwo hFit output]
  unfold outputMassFrom
  apply iSup_le
  intro steps
  exact ((finite steps).2 output).trans (le_iSup (fun k =>
    ((evalConfigWithin program (Configuration.initial (request n modulus generator q)) k).map
      report) (some output)) (used+steps+1))

/-- The entire framed sampler has polynomial expected native transition
cost: deterministic preparation plus a linear sampling/padding allowance.
Unbounded rejection branches remain present in its operational semantics. -/
theorem expectedSteps_from_frame (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    expectedSteps program (request n modulus generator q) ≤
      ((FramedScalarInput.validBudget n modulus generator + 1 + 50*(n+4) : Nat) : ℝ≥0∞) := by
  obtain ⟨used, hUsed, finite⟩ := finite_law_from_frame n modulus generator q hWidth (by omega) hFit
  rw [← expectedStepsFrom_initial]
  have tailBound : (∑' steps : Nat, timeoutProbabilityFrom program
      (Configuration.initial (request n modulus generator q)) (steps+(used+1))) ≤
      expectedStepsFrom ScalarSamplerContinuation.program
        (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits) := by
    apply ENNReal.tsum_le_tsum
    intro steps
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (finite steps).1
  have splitBound : expectedStepsFrom program (Configuration.initial (request n modulus generator q)) ≤
      ((used+1 : Nat) : ℝ≥0∞) + expectedStepsFrom ScalarSamplerContinuation.program
        (RejectionSampling.Saved.initial (List.replicate (n+3) (some true)) q.bits) := by
    unfold expectedStepsFrom
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := used+1)]
    apply add_le_add _ tailBound
    calc
      _ ≤ ∑ _steps ∈ Finset.range (used+1), (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun steps _ => PMF.coe_le_one _ _)
      _ = _ := by simp
  calc
    _ ≤ ((used+1 : Nat) : ℝ≥0∞) + ((50*((n+3)+1) : Nat) : ℝ≥0∞) :=
      splitBound.trans (add_le_add le_rfl
        (ScalarSamplerContinuation.expectedSteps_nat (n+3) q hTwo hFit))
    _ ≤ _ := by
      norm_cast
      omega

theorem almostSureHalts_from_frame (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    AlmostSureHalts program (request n modulus generator q) := by
  apply almostSureHalts_of_expectedSteps_ne_top
  exact ne_of_lt ((expectedSteps_from_frame n modulus generator q hWidth hTwo hFit).trans_lt
    (ENNReal.natCast_lt_top _))

/-- The probability-one stopping certificate exposes the ordinary unbounded
machine evaluator directly as the fixed-width uniform scalar PMF. -/
theorem evalLimit_from_frame (n : Nat) (modulus generator : List Bool) (q : Nat)
    [NeZero q] (hWidth : modulus.length = n+3) (hTwo : 2 ≤ q) (hFit : q < 2^(n+3)) :
    evalLimit program (request n modulus generator q)
      (almostSureHalts_from_frame n modulus generator q hWidth hTwo hFit) =
      (Foundation.Probability.uniform (Fin q)).map (fun a => Binary.encode (n+3) a.val) := by
  apply PMF.ext
  intro bits
  exact outputMass_from_frame n modulus generator q hWidth hTwo hFit bits

/-- The public fixed-width preparation allowance and sampling allowance form
one polynomial bound, including when the chosen modulus is small. -/
theorem expectedBudget_fixedWidth_polynomiallyBounded (modulus generator : Nat → Nat) :
    PolynomiallyBounded (fun n => FramedScalarInput.validBudget n
      (Binary.encode (n+3) (modulus n)) (Binary.encode (n+3) (generator n)) + 1 + 50*(n+4)) := by
  exact ((FramedScalarInput.validBudget_fixedWidth_polynomiallyBounded modulus generator).add
    (PolynomiallyBounded.const 1)).add
      ((PolynomiallyBounded.const 50).mul
        (PolynomiallyBounded.id.add (PolynomiallyBounded.const 4)))

end Machine.FramedScalarSampler
