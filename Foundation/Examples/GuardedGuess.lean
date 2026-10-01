import Foundation.Constructions.ElGamal.MachineNormalization
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

open GuardedCompiler

example : (guessCompile haltImmediately).length = 264 := by
  rw [guessCompile_length]
  rfl

example : (guessCompile randomOutputBit).length = 332 := by
  rw [guessCompile_length]
  rfl

example : guessTraceBudget (fun _ => 1) 0 = 264 := rfl
example : guessTraceBudget (fun _ => 2) 0 = 405 := rfl

example (saved : List (Option Bool)) (challenge : Bool) :
    ∀ c, PaddedRunsFor (guessCompile randomOutputBit)
      (packInputStart saved [some challenge] []) c 405 → c.halted = true :=
  guessCompile_haltsFrom randomOutputBit [] saved challenge (fun _ => 2)
    randomOutputBit_haltsWithin

/-- The real random source call is retained in the output PMF. A one-bit
raw source output is not a tagged guess, so the adapter fallback applies. -/
example (saved : List (Option Bool)) (challenge : Bool) :
    (evalConfigWithin (guessCompile randomOutputBit)
      (packInputStart saved [some challenge] []) 405).map Configuration.outputBits =
      Foundation.Probability.sampleBit.map
        (fun bit => [taggedGuessValue [bit] == challenge]) := by
  have h := guessCompile_evalOutput randomOutputBit [] saved challenge (fun _ => 2)
    randomOutputBit_haltsWithin
  change (evalConfigWithin (guessCompile randomOutputBit)
    (packInputStart saved [some challenge] []) 405).map Configuration.outputBits =
      (evalWithin randomOutputBit [] 2).map
        (fun output => [(match output with | some bits => taggedGuessValue bits | none => false) == challenge]) at h
  rw [randomOutputBit_eval, PMF.map_comp] at h
  exact h

example (q : Nat → Nat) (m : Nat) :
    guessTraceBudget q m ≤ 200 * (m + 1) * (q m + 1) ^ 2 := guessTraceBudget_bound q m

example (q : Nat → Nat) (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (guessTraceBudget q) := guessTraceBudget_polynomiallyBounded hq

example (E : FiniteBitEncoding Bool) (source : Program) (input : List Bool)
    (saved : List (Option Bool)) (challenge : Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    (evalConfigWithin (guessCompile source) (packInputStart saved [some challenge] input)
      (guessTraceBudget q input.length)).map Configuration.outputBits =
      (evalWithin source input (q input.length)).map
        (fun output => [(match output with
          | some bits => ElGamal.interpretGuessResponse E bits
          | none => false) == challenge]) :=
  ElGamal.guessCompile_correct E source input saved challenge q halts

end Machine.Examples
