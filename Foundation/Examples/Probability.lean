import Foundation.Crypto.Semantics.Probability.Comp

namespace Foundation.Examples.Probability

open Foundation.Probability

example (x : Nat) : eventProb (pure x : ProbComp Nat) (· = x) = 1 := by
  change (PMF.pure x).toOuterMeasure {x} = 1
  rw [PMF.toOuterMeasure_apply_singleton]
  exact PMF.pure_apply_self x

example (p : ProbComp Bool) : eventProb p (fun _ => False) = 0 := by
  simp [eventProb]

example : eventProb sampleBit (· = true) = 1 / 2 := by
  simp [eventProb, sampleBit, uniform]

example : eventProb sampleBit (· = false) = 1 / 2 := by
  simp [eventProb, sampleBit, uniform]

example : (sampleBit.bind pure) = sampleBit := PMF.bind_pure _

/-- Two successive binds are two fresh fair draws. -/
noncomputable def twoBits : ProbComp (Bool × Bool) :=
  sampleBit.bind fun a => sampleBit.bind fun b => PMF.pure (a, b)

example : eventProb twoBits (fun x => x.1 = true ∧ x.2 = true) = 1 / 4 := by
  have hset : ({x : Bool × Bool | x.1 = true ∧ x.2 = true} : Set (Bool × Bool)) = {(true, true)} := by
    ext x
    cases x with
    | mk a b => cases a <;> cases b <;> simp
  rw [eventProb, hset, PMF.toOuterMeasure_apply_singleton]
  simp [twoBits, sampleBit, uniform, PMF.bind_apply, tsum_fintype]
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

/-- Guessing a fresh fair bit with a fixed answer is unbiased. -/
noncomputable def fixedGuess : ProbComp Bool :=
  sampleBit.bind fun bit => PMF.pure (bit == true)

example : eventProb fixedGuess (· = true) = 1 / 2 := by
  have hset : ({x : Bool | x = true} : Set Bool) = {true} := rfl
  rw [eventProb, hset, PMF.toOuterMeasure_apply_singleton]
  simp [fixedGuess, sampleBit, uniform]

end Foundation.Examples.Probability
