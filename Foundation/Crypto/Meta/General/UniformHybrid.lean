import Foundation.Crypto.Semantics.Security.ThreeGames
import Foundation.Crypto.Semantics.Asymptotic.Negligible
import Foundation.Crypto.Semantics.Oracle.CountedLoop

/-! Parameter-dependent hybrid bounds require a common bound over every
index selected at that parameter. A negligible bound for each fixed index
separately does not provide this hypothesis. -/
namespace CryptoLogic.General.UniformHybrid

open Foundation.Probability
open scoped ENNReal

/-- Telescoping with arbitrary edge bounds, including the empty chain. -/
theorem telescoping (p : Nat → ℝ≥0∞) (ε : Nat → ℝ≥0∞) (count : Nat)
    (h : ∀ i < count, probabilityGap (p i) (p (i + 1)) ≤ ε i) :
    probabilityGap (p 0) (p count) ≤ ∑ i ∈ Finset.range count, ε i := by
  induction count with
  | zero => simp [probabilityGap]
  | succ count ih =>
      calc
        probabilityGap (p 0) (p (count + 1)) ≤
            probabilityGap (p 0) (p count) + probabilityGap (p count) (p (count + 1)) :=
          ThreeGames.probabilityGap_triangle _ _ _
        _ ≤ (∑ i ∈ Finset.range count, ε i) + ε count :=
          add_le_add (ih (fun i hi => h i (by omega))) (h count (by omega))
        _ = ∑ i ∈ Finset.range (count + 1), ε i := by rw [Finset.sum_range_succ]

/-- The number of hybrid edges is input data, not a code-size parameter. -/
theorem bounded (p : Nat → Nat → ℝ≥0∞) (q : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < q n → probabilityGap (p n i) (p n (i + 1)) ≤ ε n) :
    ∀ n, probabilityGap (p n 0) (p n (q n)) ≤ (q n : ℝ≥0∞) * ε n := by
  intro n
  have ht := telescoping (p n) (fun _ => ε n) (q n) (h n)
  simpa [Finset.sum_const, nsmul_eq_mul] using ht

/-- Uniform negligible edge loss times a polynomial number of edges. -/
theorem negligible (p : Nat → Nat → ℝ≥0∞) (q : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < q n → probabilityGap (p n i) (p n (i + 1)) ≤ ε n)
    (hq : PolynomiallyBounded q) (hε : Negligible ε) :
    Negligible (fun n => probabilityGap (p n 0) (p n (q n))) :=
  Negligible.mono (bounded p q ε h) (Negligible.mul_polynomial hε hq)

/-- Acceptance probability of the same fixed eight-instruction machine in
an indexed oracle world. Only public input data and the oracle world vary. -/
noncomputable def loopProbability {State : Type} (world : Nat → Nat →
    CryptoOracle.CountedLoop.BoolOracle State) (state : Nat → State)
    (queries : Nat → Nat) (n index : Nat) : ℝ≥0∞ :=
  eventProb (CryptoOracle.Interactive.eval CryptoOracle.CountedLoop.code
    (CryptoOracle.CountedLoop.bitOracle (world n index))
    (CryptoOracle.Interactive.Configuration.initial (state n)
      (List.replicate (queries n) true)) (14 * queries n + 6))
    (fun out => out.result = some true)

/-- Uniform edge bounds for actual executions imply the variable-length
hybrid bound. This uses no security-parameter-dependent code construction. -/
theorem executed_bounded {State : Type} (world : Nat → Nat →
    CryptoOracle.CountedLoop.BoolOracle State) (state : Nat → State)
    (queries edges : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < edges n → probabilityGap
      (loopProbability world state queries n i)
      (loopProbability world state queries n (i + 1)) ≤ ε n) :
    ∀ n, probabilityGap (loopProbability world state queries n 0)
      (loopProbability world state queries n (edges n)) ≤ (edges n : ℝ≥0∞) * ε n :=
  bounded (loopProbability world state queries) edges ε h

/-- The very same code realizing the hybrid probabilities genuinely stops
within the polynomial budget and makes exactly the declared query count
in every world, including the endpoints. -/
theorem executed_resources {State : Type} (world : Nat → Nat →
    CryptoOracle.CountedLoop.BoolOracle State) (state : Nat → State)
    (queries : Nat → Nat) (hq : PolynomiallyBounded queries) :
    PolynomiallyBounded (fun n => 14 * queries n + 6) ∧
    ∀ n i, CryptoOracle.Interactive.HaltsWithin CryptoOracle.CountedLoop.code
      (CryptoOracle.CountedLoop.bitOracle (world n i))
      (CryptoOracle.Interactive.Configuration.initial (state n)
        (List.replicate (queries n) true)) (14 * queries n + 6) ∧
      ∀ out ∈ (CryptoOracle.Interactive.eval CryptoOracle.CountedLoop.code
        (CryptoOracle.CountedLoop.bitOracle (world n i))
        (CryptoOracle.Interactive.Configuration.initial (state n)
          (List.replicate (queries n) true)) (14 * queries n + 6)).support,
        out.reverseTrace.length = queries n := by
  refine ⟨CryptoOracle.CountedLoop.profile_time_polynomial hq, ?_⟩
  intro n i
  exact ⟨CryptoOracle.CountedLoop.halts _ _ _, CryptoOracle.CountedLoop.queries _ _ _⟩

/-- Polynomially many edges with a common negligible loss yield negligible
endpoint separation for these finite-code executions. -/
theorem executed_negligible {State : Type} (world : Nat → Nat →
    CryptoOracle.CountedLoop.BoolOracle State) (state : Nat → State)
    (queries edges : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < edges n → probabilityGap
      (loopProbability world state queries n i)
      (loopProbability world state queries n (i + 1)) ≤ ε n)
    (he : PolynomiallyBounded edges) (hε : Negligible ε) :
    Negligible (fun n => probabilityGap (loopProbability world state queries n 0)
      (loopProbability world state queries n (edges n))) :=
  negligible (loopProbability world state queries) edges ε h he hε


end CryptoLogic.General.UniformHybrid
