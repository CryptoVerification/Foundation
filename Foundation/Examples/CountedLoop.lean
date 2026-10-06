import Foundation.Crypto.Meta.General.UniformHybrid

namespace CryptoOracle.CountedLoopExamples
open Interactive CountedLoop
open scoped ENNReal

/-- A deterministic fixture flips each request, so later requests verify
that the finite machine uses previous replies adaptively. -/
def flipOracle (state : Nat) (request : List Bool) : Nat × List Bool :=
  (state + 1, [!(request.headD false)])

/-- info: (some false, 6, 0, []) -/
#guard_msgs in
#eval
  let (out, used) := simulate code flipOracle false 6 (Configuration.initial 0 [])
  (out.result, used, out.state, out.reverseTrace.reverse)

/-- info: (some true, 20, 1, [([false], [true])]) -/
#guard_msgs in
#eval
  let (out, used) := simulate code flipOracle false 20
    (Configuration.initial 0 (List.replicate 1 true))
  (out.result, used, out.state, out.reverseTrace.reverse)

/-- info: (some false, 62, 4, [([false], [true]), ([true], [false]), ([false], [true]), ([true], [false])]) -/
#guard_msgs in
#eval
  let (out, used) := simulate code flipOracle false 62
    (Configuration.initial 0 (List.replicate 4 true))
  (out.result, used, out.state, out.reverseTrace.reverse)

/-- info: (none, 61, 4) -/
#guard_msgs in
#eval
  let (out, used) := simulate code flipOracle false 61
    (Configuration.initial 0 (List.replicate 4 true))
  (out.result, used, out.state)

example {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (fun n => 14 * q n + 6) := profile_time_polynomial hq

example (p : Nat → Nat → ℝ≥0∞) (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < n * n →
      Foundation.Probability.probabilityGap (p n i) (p n (i + 1)) ≤ ε n)
    (hε : Negligible ε) :
    Negligible (fun n => Foundation.Probability.probabilityGap (p n 0) (p n (n * n))) :=
  CryptoLogic.General.UniformHybrid.negligible p (fun n => n * n) ε h
    (PolynomiallyBounded.id.mul PolynomiallyBounded.id) hε

/-- Both the changing edge count and the changing query count are tied to
probabilities of the actual fixed-code execution, rather than fresh code. -/
example {State : Type} (world : Nat → Nat → BoolOracle State) (state : Nat → State)
    (ε : Nat → ℝ≥0∞)
    (h : ∀ n i, i < n → Foundation.Probability.probabilityGap
      (CryptoLogic.General.UniformHybrid.loopProbability world state (fun n => n * n) n i)
      (CryptoLogic.General.UniformHybrid.loopProbability world state (fun n => n * n) n (i + 1)) ≤ ε n)
    (hε : Negligible ε) :
    Negligible (fun n => Foundation.Probability.probabilityGap
      (CryptoLogic.General.UniformHybrid.loopProbability world state (fun n => n * n) n 0)
      (CryptoLogic.General.UniformHybrid.loopProbability world state (fun n => n * n) n n)) :=
  CryptoLogic.General.UniformHybrid.executed_negligible world state (fun n => n * n)
    (fun n => n) ε h PolynomiallyBounded.id hε

example {State : Type} (oracle : BoolOracle State) (state : State) (n : Nat) :
    Interactive.HaltsWithin code (bitOracle oracle)
      (Configuration.initial state (List.replicate (n * n) true)) (14 * (n * n) + 6) :=
  halts oracle state (n * n)

end CryptoOracle.CountedLoopExamples
