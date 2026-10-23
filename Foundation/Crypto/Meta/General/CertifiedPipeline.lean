import Foundation.Crypto.Logic.General.ResourceImprovement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite prefixes of certified compiler chains retain their actual emitted
code and all execution evidence. Additive resource envelopes allow variable
depth without a constant-depth assumption. Observations are supplied for
each backend's original resource type; the theorem does not identify units
between machines. Selecting a prefix by the security parameter may select
different code, so uniform compilation is a separate obligation. -/
namespace CryptoLogic.General.CertifiedPipeline
universe u v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {K : CodeSystem} {m : K.Machine}

structure Entry (X : SecurityObject.{u, v} K m) where
  family : InstanceFamily X.goal
  adversary : AdversaryFamily X.goal family
  witness : X.Witness family adversary

-- Entry itself is independent of a particular index in the chain.
end CryptoLogic.General.CertifiedPipeline

namespace CryptoLogic.General.CertifiedPipeline
universe u v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {K : CodeSystem} {machine : Nat → K.Machine}
  {X : ∀ i, SecurityObject.{u, v} K (machine i)}
  (stage : ∀ i, CertifiedTransform (X i) (X (i + 1)))

def advance (i : Nat) (entry : Entry (X i)) : Entry (X (i + 1)) :=
  ⟨(stage i).transform.mapFamily entry.family,
    (stage i).transform.mapAdversaryFamily entry.family entry.adversary,
    (stage i).mapWitness entry.family entry.adversary entry.witness⟩

def run (input : Entry (X 0)) : (i : Nat) → Entry (X i)
  | 0 => input
  | i + 1 => advance stage i (run input i)

/-- Actual finite compiler syntax, independent of witness values. -/
def compiler : (i : Nat) → Compiler K (machine 0) (machine i)
  | 0 => .identity (machine 0)
  | i + 1 => .comp (compiler i) (stage i).compiler

theorem code (input : Entry (X 0)) (i : Nat) :
    (run stage input i).witness.code = (compiler stage i).run input.witness.code := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change ((stage i).mapWitness _ _ (run stage input i).witness).code = _
      rw [(stage i).code_eq, ih]
      rfl

/-- Execution and realization refer to the very same emitted code; the
original resource value and admissibility proof are carried by run.witness. -/
theorem executes (input : Entry (X 0)) (i : Nat) :
    (X i).execution.ExecutesWithin (run stage input i).family
      ((compiler stage i).run input.witness.code) (run stage input i).witness.resources := by
  rw [← code stage input i]
  exact (run stage input i).witness.executes

theorem realizes (input : Entry (X 0)) (i : Nat) :
    (X i).execution.Realizes (run stage input i).family (run stage input i).adversary
      ((compiler stage i).run input.witness.code) (run stage input i).witness.resources := by
  rw [← code stage input i]
  exact (run stage input i).witness.realizes

/-- A chosen scalar observation is for analysis only. A time observation
must be justified by the backend's execution contract before interpreting
the resulting inequality as a time bound. Other resource values are retained. -/
theorem accumulated
    (observe : ∀ i, (X i).execution.Resources → Nat → Nat) (charge : Nat → Nat → Nat)
    (localBound : ∀ i (entry : Entry (X i)) size,
      observe (i + 1) (advance stage i entry).witness.resources size ≤
        observe i entry.witness.resources size + charge i size)
    (input : Entry (X 0)) (depth size : Nat) :
    observe depth (run stage input depth).witness.resources size ≤
      observe 0 input.witness.resources size + ∑ i ∈ Finset.range depth, charge i size := by
  induction depth with
  | zero => simp [run]
  | succ depth ih =>
      have one := localBound depth (run stage input depth) size
      change observe (depth + 1) (advance stage depth (run stage input depth)).witness.resources size ≤ _
      calc
        _ ≤ observe depth (run stage input depth).witness.resources size + charge depth size := one
        _ ≤ (observe 0 input.witness.resources size +
            ∑ i ∈ Finset.range depth, charge i size) + charge depth size := Nat.add_le_add_right ih _
        _ = _ := by rw [Finset.sum_range_succ, Nat.add_assoc]

/-- Uniform additive charges, rather than a fixed bound on proof depth,
suffice for a polynomial observed-resource envelope. This is not a theorem
that the parameter-indexed emitted-code family is one uniform program. -/
theorem polynomial_envelope
    (observe : ∀ i, (X i).execution.Resources → Nat → Nat) (charge : Nat → Nat → Nat)
    (localBound : ∀ i (entry : Entry (X i)) size,
      observe (i + 1) (advance stage i entry).witness.resources size ≤
        observe i entry.witness.resources size + charge i size)
    (input : Entry (X 0)) (depth overhead : Nat → Nat)
    (hUniform : ∀ size i, i < depth size → charge i size ≤ overhead size)
    (hInput : PolynomiallyBounded (observe 0 input.witness.resources))
    (hDepth : PolynomiallyBounded depth) (hOverhead : PolynomiallyBounded overhead) :
    PolynomiallyBounded (fun size => observe (depth size)
      (run stage input (depth size)).witness.resources size) := by
  apply PolynomiallyBounded.mono _ (hInput.add (hDepth.mul hOverhead))
  intro size
  have sumBound : (∑ i ∈ Finset.range (depth size), charge i size) ≤ depth size * overhead size := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (depth size), overhead size := by
        apply Finset.sum_le_sum
        intro i hi
        exact hUniform size i (Finset.mem_range.mp hi)
      _ = _ := by simp
  exact (accumulated stage observe charge localBound input (depth size) size).trans
    (Nat.add_le_add_left sumBound _)

/-- Per-stage polynomiality alone is not a useful uniform additive charge:
repeated doubling grows exponentially already at the resource recurrence. -/
theorem doubling (depth : Nat) : ((fun cost : Nat => 2 * cost)^[depth]) 1 = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ, Nat.mul_comm]

end CryptoLogic.General.CertifiedPipeline
