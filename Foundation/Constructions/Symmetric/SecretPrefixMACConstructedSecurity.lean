import Foundation.Constructions.Symmetric.SecretPrefixMACReduction
import Foundation.Constructions.Hash.QueryIndifferentiability

/-! Instantiation of the existing single-stage MAC reduction with the proved
prefix-free MD theorem. This module concerns the existing hash-and-tag attacker
interface; it does not yet add a public compression window to the MAC attacker. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The secret-prefix MAC using the implemented prefix-free MD over an ideal
compression function is unforgeable for the existing hash-and-tag adversaries.
The additional final verification call and its key/terminal blocks are counted.
There is no assumed indifferentiability premise in this theorem. -/
theorem constructed_security {κ n hashLength messageLength qH qT blockLimit : Nat}
    (initial : Bits n) (terminal : Bits κ) (messageLimit : Nat)
    (attack : Attack κ n) (budget : Budget hashLength messageLength attack qH qT)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    let queries := qH + qT + 1
    let Q := queries * blockLimit
    eventProb (constructedGame initial terminal messageLimit attack) (· = true) ≤
      qH * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹ +
      ((Q * (Q + 1) + (2 * Q * (Q + 1) + queries * Q) : Nat) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have secure := Foundation.Hash.prefixFreeMD_query_indifferentiable initial terminal blockLimit (qH + qT + 1)
  have result := constructed_security_of_indifferentiable initial terminal messageLimit _
    attack budget hashBlocks signBlocks finalBlocks secure
  simpa [Bits, Fintype.card_fun] using result

end Foundation.Symmetric.SecretPrefixMAC
