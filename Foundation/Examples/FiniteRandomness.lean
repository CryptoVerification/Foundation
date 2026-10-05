import Foundation.Crypto.Semantics.Machine.FiniteRandomness
import Foundation.Crypto.Semantics.Machine.Adversary
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

open Foundation.Probability

/-- Two outputs are possible with one actual fair random instruction;
ignored padding bits do not impose an extra operational cost. -/
example : (evalWithin randomOutputBit [] 2).map
    (fun bits => bits.bind FiniteBitEncoding.bool.decode) = (uniform Bool).map some := by
  rw [randomOutputBit_eval, PMF.map_comp]
  rfl

example : Fintype.card Bool ∣ 2 ^ 2 := by
  apply card_dvd_pow_two_of_exact_uniform randomOutputBit [] 2 FiniteBitEncoding.bool.decode
  rw [randomOutputBit_eval, PMF.map_comp]
  rfl

/-- Three equally likely outputs cannot be produced at any fixed finite
budget, even with an arbitrary mathematical decoder. -/
example (p : Program) (input : List Bool) (rounds : Nat)
    (decode : List Bool → Option (Fin 3)) :
    (evalWithin p input rounds).map (fun bits => bits.bind decode) ≠
      (uniform (Fin 3)).map some := by
  apply no_exact_uniform_of_odd_prime_card
    (by simpa using Nat.prime_three) (by norm_num)

end Machine.Examples
