import Foundation.Constructions.Symmetric.SecretPrefixMACMergeBudget

/-! One-stage secret-prefix MAC security after replacing the RO by the proved
prefix-free MD construction, including public compression queries. The fixed
simulator is merged into an actual ROM attacker with proved call/length growth.
No machine-time or encoded-memory bound is asserted by these query theorems. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The simulated compression window adds at most qC public hash queries to
the ordinary ROM MAC attacker. Simulator and adversary share state throughout. -/
theorem simulated_rom_security {κ n hashLength messageLength qH qT qC : Nat}
    (initial : Bits n) (terminal : Bits κ) (messageLimit : Nat) (attack : PublicAttack κ n)
    (budget : PublicBudget hashLength messageLength attack qH qT qC) :
    eventProb (publicGame ((Foundation.Hash.candidate initial terminal).world RandomOracle.oracle)
      ([], []) messageLimit attack) (· = true) ≤
      (qH + qC) * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [← mergeAttack_game RandomOracle.oracle initial terminal [] [] messageLimit attack]
  simpa only [successProbability, romGame, Nat.cast_add] using
    rom_security_bits messageLimit (mergeAttack initial terminal [] attack)
      (budget.merged_from_empty initial terminal)

/-- Explicit compression-call budget of the actual world distinguisher,
including its final verification, all high-level expansion, and public low calls. -/
theorem public_reduction_compression_queries {κ n hashLength messageLength qH qT qC blockLimit : Nat}
    (initial : Bits n) (terminal : Bits κ) (messageLimit : Nat) (attack : PublicAttack κ n)
    (budget : PublicBudget hashLength messageLength attack qH qT qC)
    (positive : 1 ≤ blockLimit)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    (Foundation.Hash.expand initial terminal (publicDistinguisher messageLimit attack)).BoundedQueries
      ((qH + qT + qC + 1) * blockLimit) :=
  (budget.distinguisher_bound messageLimit blockLimit positive hashBlocks signBlocks finalBlocks).expanded_queries
    initial terminal

/-- Concrete EUF-CMA bound with public access to both the constructed hash
and its ideal compression function. The attack, signing, and final verification
form one shared-state execution. Only unsigned in-domain messages can win.
The final verification and key/terminal blocks are explicitly included.
There is no assumed hash security premise or attacker-specific simulator. -/
theorem public_constructed_security {κ n hashLength messageLength qH qT qC blockLimit : Nat}
    (initial : Bits n) (terminal : Bits κ) (messageLimit : Nat) (attack : PublicAttack κ n)
    (budget : PublicBudget hashLength messageLength attack qH qT qC)
    (positive : 1 ≤ blockLimit)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    let queries := qH + qT + qC + 1
    let Q := queries * blockLimit
    eventProb (publicConstructedGame initial terminal messageLimit attack) (· = true) ≤
      (qH + qC) * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹ +
      ((Q * (Q + 1) + (2 * Q * (Q + 1) + queries * Q) : Nat) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  let queries := qH + qT + qC + 1
  let Q := queries * blockLimit
  let error : ℝ≥0∞ := ((Q * (Q + 1) + (2 * Q * (Q + 1) + queries * Q) : Nat) : ℝ≥0∞) *
    ((2 : ℝ≥0∞) ^ n)⁻¹
  have bounded := budget.distinguisher_bound messageLimit blockLimit positive hashBlocks signBlocks finalBlocks
  have gap := Foundation.Hash.candidate_gap_bound bounded initial terminal (List.finRange Q)
    (List.nodup_finRange _) (by simp [Q, queries]) initial (fun result => result = true)
  have observed : probabilityGap
      (eventProb (publicConstructedGame initial terminal messageLimit attack) (· = true))
      (eventProb (publicGame ((Foundation.Hash.candidate initial terminal).world RandomOracle.oracle)
        ([], []) messageLimit attack) (· = true)) ≤ error := by
    change probabilityGap
      (eventProb (publicGame (Foundation.Hash.realWorld initial terminal) [] messageLimit attack) (· = true)) _ ≤ _
    rw [← publicDistinguisher_run (Foundation.Hash.realWorld initial terminal) [] messageLimit attack,
      ← publicDistinguisher_run ((Foundation.Hash.candidate initial terminal).world RandomOracle.oracle)
        ([], []) messageLimit attack]
    simpa [eventProb_map, Fintype.card_fin, error, Q, queries, Bits, Fintype.card_fun] using gap
  have oneSide : eventProb (publicConstructedGame initial terminal messageLimit attack) (· = true) ≤
      error + eventProb (publicGame ((Foundation.Hash.candidate initial terminal).world RandomOracle.oracle)
        ([], []) messageLimit attack) (· = true) := by
    apply tsub_le_iff_right.mp
    exact (le_max_left _ _).trans observed
  calc
    _ ≤ error + eventProb (publicGame ((Foundation.Hash.candidate initial terminal).world RandomOracle.oracle)
        ([], []) messageLimit attack) (· = true) := oneSide
    _ ≤ error + ((qH + qC) * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹) :=
      add_le_add (le_refl _) (simulated_rom_security initial terminal messageLimit attack budget)
    _ = _ := add_comm _ _

end Foundation.Symmetric.SecretPrefixMAC
