import Foundation.Machine.LimitExecution
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

open Foundation.Probability
open scoped ENNReal

/-- The unbounded evaluator agrees with a terminating deterministic program. -/
example (input : List Bool) :
    (evalLimit haltImmediately input
      (haltImmediately_haltsWithin input).almostSureHalts).map some =
      PMF.pure (some []) := by
  rw [evalLimit_map_some_of_haltsWithin (haltImmediately_haltsWithin input)]
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
    haltImmediately, Configuration.initial, Configuration.outputBits,
    Tape.bits, PMF.pure_map]

/-- The limiting distribution preserves the exact fair-bit output law. -/
example :
    (evalLimit randomOutputBit [] randomOutputBit_haltsWithin.almostSureHalts).map some =
      sampleBit.map (fun bit => some [bit]) := by
  rw [evalLimit_map_some_of_haltsWithin randomOutputBit_haltsWithin]
  exact randomOutputBit_eval

/-- A genuinely nonhalting finite program, used to check that timeout mass
is not automatically converted to a normalized output distribution. -/
def loopForever : Program := [.jump 0]

private theorem loopForever_evalConfig (input : List Bool) (steps : Nat) :
    evalConfigWithin loopForever (Configuration.initial input) steps =
      PMF.pure (Configuration.initial input) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [evalConfigWithin, ih]
      simp [stepPMF, next, loopForever, Configuration.initial, Instruction.next]

private theorem loopForever_evalWithin (input : List Bool) (steps : Nat) :
    evalWithin loopForever input steps = PMF.pure none := by
  unfold evalWithin
  rw [loopForever_evalConfig]
  simp [PMF.pure_map, Configuration.initial]

example (input bits : List Bool) : outputMass loopForever input bits = 0 := by
  simp [outputMass, loopForever_evalWithin]

example (input : List Bool) : expectedSteps loopForever input = ∞ := by
  simp [expectedSteps, timeoutProbability, eventProb, loopForever_evalWithin]

example (input : List Bool) : ¬ AlmostSureHalts loopForever input := by
  intro h
  have hTimeout : timeoutProbability loopForever input = fun _ => 1 := by
    funext steps
    simp [timeoutProbability, eventProb, loopForever_evalWithin]
  change Filter.Tendsto (timeoutProbability loopForever input) Filter.atTop (nhds 0) at h
  rw [hTimeout] at h
  have hEq : (1 : ℝ≥0∞) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  exact one_ne_zero hEq

end Machine.Examples
