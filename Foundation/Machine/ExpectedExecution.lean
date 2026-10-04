import Foundation.Machine.PolynomialTime

namespace Machine

open Foundation.Probability
open scoped ENNReal Topology

/-- Probability that execution has not halted after `steps` actual transitions.
The finite evaluator absorbs halted configurations; those inspection stutters
do not create additional operational transitions. -/
noncomputable def timeoutProbability (p : Program) (input : List Bool)
    (steps : Nat) : ℝ≥0∞ :=
  eventProb (evalWithin p input steps) (· = none)

/-- Expected number of operational transitions, expressed as the tail sum of
the halting time. The term at zero is included, so executing one halt
instruction costs one transition. Infinite expectation is permitted here.
This definition does not yet construct an unbounded output distribution. -/
noncomputable def expectedSteps (p : Program) (input : List Bool) : ℝ≥0∞ :=
  ∑' steps : Nat, timeoutProbability p input steps

theorem timeoutProbability_le_one (p : Program) (input : List Bool) (steps : Nat) :
    timeoutProbability p input steps ≤ 1 := by
  change (evalWithin p input steps).toOuterMeasure {none} ≤ 1
  rw [PMF.toOuterMeasure_apply_singleton]
  exact PMF.coe_le_one _ _

/-- Every-branch halting within a fixed bound also bounds the expected number
of transitions. This implication does not assume a converse. -/
theorem expectedSteps_le_of_haltsWithin {p : Program} {input : List Bool}
    {bound : Nat} (h : HaltsWithin p input bound) :
    expectedSteps p input ≤ (bound : ℝ≥0∞) := by
  unfold expectedSteps
  rw [tsum_eq_sum (s := Finset.range bound) (fun steps hSteps => by
    apply evalWithin_no_timeout
    exact h.mono (Nat.le_of_not_gt (by simpa using hSteps)))]
  calc
    ∑ steps ∈ Finset.range bound, timeoutProbability p input steps
        ≤ ∑ _steps ∈ Finset.range bound, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun steps _ => timeoutProbability_le_one p input steps)
    _ = (bound : ℝ≥0∞) := by simp

/-- The chance of still running tends to zero. This concerns probability,
and does not assert that every infinite sequence of random choices halts. -/
def AlmostSureHalts (p : Program) (input : List Bool) : Prop :=
  Filter.Tendsto (timeoutProbability p input) Filter.atTop (𝓝 0)

theorem almostSureHalts_of_expectedSteps_ne_top {p : Program} {input : List Bool}
    (h : expectedSteps p input ≠ ∞) : AlmostSureHalts p input :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top h

theorem HaltsWithin.almostSureHalts {p : Program} {input : List Bool}
    {bound : Nat} (h : HaltsWithin p input bound) : AlmostSureHalts p input := by
  apply almostSureHalts_of_expectedSteps_ne_top
  exact ne_of_lt ((expectedSteps_le_of_haltsWithin h).trans_lt
    (ENNReal.natCast_lt_top _))

/-- Expected transition count is polynomially bounded in total input bit
length, for one fixed finite program on all inputs. This is separate from
the existing every-branch `PolynomialTime` property. -/
def ExpectedPolynomialTime (p : Program) : Prop :=
  ∃ q : Nat → Nat,
    PolynomiallyBounded q ∧
    ∀ input : List Bool, expectedSteps p input ≤ (q input.length : ℝ≥0∞)

theorem PolynomialTime.expectedPolynomialTime {p : Program}
    (h : PolynomialTime p) : ExpectedPolynomialTime p := by
  obtain ⟨q, hq, hHalt⟩ := h
  exact ⟨q, hq, fun input => expectedSteps_le_of_haltsWithin (hHalt input)⟩

theorem ExpectedPolynomialTime.almostSureHalts {p : Program}
    (h : ExpectedPolynomialTime p) (input : List Bool) : AlmostSureHalts p input := by
  obtain ⟨q, _, hBound⟩ := h
  apply almostSureHalts_of_expectedSteps_ne_top
  exact ne_of_lt ((hBound input).trans_lt (ENNReal.natCast_lt_top _))

end Machine
