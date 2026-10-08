import Foundation.Constructions.Symmetric.PRFCounterPrivacy

namespace Foundation.Symmetric.PRFCounterExamples
open CryptoOracle Foundation.Probability PRFCounter
open scoped ENNReal

def threeRequests : Attack 1 :=
  .query (fun _ => false, fun _ => true) (fun _ =>
    .query (fun _ => true, fun _ => false) (fun _ =>
      .query (fun _ => false, fun _ => true) (fun reply => .done reply.isNone)))

/-- A capacity of two explicitly rejects the third encryption. -/
example (table : Fin 2 → Bits 1) (right : Bool) :
    (threeRequests.run (oracle table right) 0).map Outcome.result = PMF.pure true := by
  simp [threeRequests, Program.run, oracle, PMF.pure_map]

/-- Three encryption requests produce at most two PRF queries after exhaustion. -/
example (right : Bool) :
    (reduce (capacity := 2) right 0 threeRequests).BoundedQueries 2 := by
  simp only [threeRequests, reduce, show 0 < 2 by decide, show 1 < 2 by decide,
    show ¬ 2 < 2 by decide, dite_true, dite_false]
  exact .query _ _ 1 (fun _ => .query _ _ 0 (fun _ => .done _ 0))

example {capacity length : Nat} (table : Fin capacity → Bits length) (right : Bool)
    (attack : Attack length) :
    PRF.runTable (reduce right 0 attack) table = runTable attack right table :=
  simulation table right 0 attack


example (S : Scheme) (n : Nat) (attack : Attack (S.length n)) :
    ideal S n false attack = ideal S n true attack := ideal_privacy S n attack

example (S : Scheme) (q : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : PRF.QuerySecure S.toPRF q ε) : QuerySecure S q (fun n => 2 * ε n) :=
  query_secure S q ε h

/-- The source attack may adapt its second plaintext to the first ciphertext
and to a fresh local coin. The theorem covers both sources of branching. -/
def adaptiveAttack : Attack 1 :=
  .query ((fun _ => false), (fun _ => true)) (fun first =>
    .coin (fun coin =>
      let bit := (first.map (fun c => c.2 0)).getD false
      .query ((fun _ => Bool.xor bit coin), (fun _ => !bit)) (fun second =>
        .done ((second.map (fun c => c.2 0)).getD false))))

example {capacity : Nat} :
    (uniform (Fin capacity → Bits 1)).bind (fun table => runTable adaptiveAttack false table) =
    (uniform (Fin capacity → Bits 1)).bind (fun table => runTable adaptiveAttack true table) := by
  exact (ideal_fresh (capacity := capacity) adaptiveAttack false 0).trans
    (ideal_fresh (capacity := capacity) adaptiveAttack true 0).symm

end Foundation.Symmetric.PRFCounterExamples
