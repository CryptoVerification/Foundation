import Foundation.Crypto.Meta.Polygraph.FiniteHybrid
import Foundation.Crypto.Meta.General.UniformHybrid

/-! Parameter-dependent experiment chains require the same bound at every
used edge. The executed instance retains one fixed finite machine and the
existing stopping and exact query-count guarantees in every oracle world. -/
namespace CryptoLogic.Polygraph.UniformHybrid

open Foundation.Probability
open scoped ENNReal

theorem bounded (games : Nat → Nat → Experiment.Observed) (count : Nat → Nat)
    (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < count n → Nonempty (Experiment.Hop (games n i) (games n (i + 1)) (ε n))) :
    ∀ n, probabilityGap (games n 0).probability (games n (count n)).probability ≤
      (count n : ℝ≥0∞) * ε n :=
  General.UniformHybrid.bounded (fun n i => (games n i).probability) count ε
    (fun n i hi => (h n i hi).elim Experiment.Hop.sound)

theorem negligible (games : Nat → Nat → Experiment.Observed) (count : Nat → Nat)
    (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < count n → Nonempty (Experiment.Hop (games n i) (games n (i + 1)) (ε n)))
    (hc : PolynomiallyBounded count) (hε : Negligible ε) :
    Negligible (fun n => probabilityGap (games n 0).probability (games n (count n)).probability) :=
  Negligible.mono (bounded games count ε h) (Negligible.mul_polynomial hε hc)

noncomputable def executedGame {State : Type}
    (world : Nat → Nat → CryptoOracle.CountedLoop.BoolOracle State)
    (state : Nat → State) (queries : Nat → Nat) (n i : Nat) : Experiment.Observed where
  Outcome := CryptoOracle.Interactive.Configuration State
  program := .sample (CryptoOracle.Interactive.eval CryptoOracle.CountedLoop.code
    (CryptoOracle.CountedLoop.bitOracle (world n i))
    (CryptoOracle.Interactive.Configuration.initial (state n) (List.replicate (queries n) true))
    (14 * queries n + 6))
  event := fun out => out.result = some true

theorem executed_probability {State : Type}
    (world : Nat → Nat → CryptoOracle.CountedLoop.BoolOracle State)
    (state : Nat → State) (queries : Nat → Nat) (n i : Nat) :
    (executedGame world state queries n i).probability =
      General.UniformHybrid.loopProbability world state queries n i := rfl

theorem executed_bounded {State : Type}
    (world : Nat → Nat → CryptoOracle.CountedLoop.BoolOracle State)
    (state : Nat → State) (queries count : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < count n → Nonempty (Experiment.Hop
      (executedGame world state queries n i) (executedGame world state queries n (i + 1)) (ε n))) :
    ∀ n, probabilityGap (General.UniformHybrid.loopProbability world state queries n 0)
      (General.UniformHybrid.loopProbability world state queries n (count n)) ≤
        (count n : ℝ≥0∞) * ε n := bounded (executedGame world state queries) count ε h

theorem executed_negligible {State : Type}
    (world : Nat → Nat → CryptoOracle.CountedLoop.BoolOracle State)
    (state : Nat → State) (queries count : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < count n → Nonempty (Experiment.Hop
      (executedGame world state queries n i) (executedGame world state queries n (i + 1)) (ε n)))
    (hc : PolynomiallyBounded count) (hε : Negligible ε) :
    Negligible (fun n => probabilityGap
      (General.UniformHybrid.loopProbability world state queries n 0)
      (General.UniformHybrid.loopProbability world state queries n (count n))) :=
  negligible (executedGame world state queries) count ε h hc hε

/-- This theorem is deliberately about the same fixed code used in the
experiment syntax, including both endpoints of every chain. -/
theorem executed_resources {State : Type}
    (world : Nat → Nat → CryptoOracle.CountedLoop.BoolOracle State)
    (state : Nat → State) (queries : Nat → Nat) (hq : PolynomiallyBounded queries) :
    PolynomiallyBounded (fun n => 14 * queries n + 6) ∧
    ∀ n i, CryptoOracle.Interactive.HaltsWithin CryptoOracle.CountedLoop.code
      (CryptoOracle.CountedLoop.bitOracle (world n i))
      (CryptoOracle.Interactive.Configuration.initial (state n) (List.replicate (queries n) true))
      (14 * queries n + 6) ∧
      ∀ out ∈ (Experiment.Program.eval (executedGame world state queries n i).program).support,
        out.reverseTrace.length = queries n :=
  General.UniformHybrid.executed_resources world state queries hq

end CryptoLogic.Polygraph.UniformHybrid
