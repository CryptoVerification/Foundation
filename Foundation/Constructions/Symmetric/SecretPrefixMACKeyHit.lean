import Foundation.Constructions.Symmetric.SecretPrefixMACSecurity
import Foundation.Crypto.Semantics.Oracle.RandomOracleReindex
import Foundation.Crypto.Semantics.Oracle.Stopping

/-! Comparison of the actual MAC interaction and the independent-domain
experiment, stopped before the first public input containing the key. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def hitsKey {κ : Nat} (key : Key κ) : Request κ → Bool
  | .inl (head :: _) => decide (head = key)
  | _ => false

theorem keyHit_iff_any {κ n : Nat} (key : Key κ) (trace : List (Request κ × Tag n)) :
    KeyHit key trace ↔ trace.any (fun e => hitsKey key e.1) = true := by
  induction trace with
  | nil => simp [KeyHit]
  | cons entry tail ih =>
      rw [List.any_cons, Bool.or_eq_true, ← ih]
      obtain ⟨request, response⟩ := entry
      cases request with
      | inr message => simp [KeyHit, hitsKey]
      | inl message =>
          cases message <;> simp [KeyHit, hitsKey, input, eq_comm, exists_or]

/-- Before the first key hit, encoding both interfaces as hash inputs is
injective. The subtype excludes the public inputs which would cause aliasing. -/
theorem allowed_input_injective {κ : Nat} (key : Key κ) :
    Function.Injective (fun request : {request : Request κ // hitsKey key request = false} =>
      requestInput key request.val) := by
  rintro ⟨left, hl⟩ ⟨right, hr⟩ he
  apply Subtype.ext
  cases left with
  | inl left =>
      cases right with
      | inl right => exact congrArg Sum.inl he
      | inr right =>
          change left = input key right at he
          rw [he] at hl
          simp [hitsKey, input] at hl
  | inr left =>
      cases right with
      | inl right =>
          change input key left = right at he
          rw [← he] at hr
          simp [hitsKey, input] at hr
      | inr right =>
          change input key left = input key right at he
          exact congrArg Sum.inr (by simpa [input] using he)

/-- Exact equality of the stopped result laws. This uses injective reindexing
of lazy random functions, not an assumption of key-independent signing replies. -/
theorem stopped_domains_eq {κ n : Nat} (key : Key κ) (attack : Attack κ n) :
    (((Program.stopBefore (hitsKey key) attack).mapQueries (requestInput key) id).run
      RandomOracle.oracle []).map Outcome.result =
    ((Program.stopBefore (hitsKey key) attack).run RandomOracle.oracle []).map
      Outcome.result := by
  rw [← Program.stopBeforeAllowed_val]
  rw [Program.mapQueries_comp]
  have left := RandomOracle.reindex_result
    (fun request : {request : Request κ // hitsKey key request = false} =>
      requestInput key request.val) (allowed_input_injective key)
    (Program.stopBeforeAllowed (hitsKey key) attack) []
  have right := RandomOracle.reindex_result Subtype.val Subtype.val_injective
    (Program.stopBeforeAllowed (hitsKey key) attack) []
  exact left.trans right.symm

/-- Forgetting only the signed-message bookkeeping gives exactly the keyed
hash-query interpreter, with the complete public transcript preserved. -/
theorem rom_run_hash_projection {κ n : Nat} (key : Key κ) (attack : Attack κ n)
    (table : RandomOracle.Table (Message κ) (Tag n)) (signed : List (Message κ)) :
    (attack.run (oracle RandomOracle.oracle key) (table, signed)).map
      (Program.mapState Prod.fst) =
    attack.run (Program.adaptOracle (requestInput key) id RandomOracle.oracle) table := by
  apply Program.run_state_map
  intro state request
  cases request <;>
    simp only [oracle, tag, requestInput, Program.adaptOracle, PMF.map_comp,
      Function.comp_def, id_eq]

/-- The two full attack experiments have equal first-key-hit probabilities.
Their replies need not agree after the hit, so no equality of full transcripts
or of the MAC success probabilities is asserted. -/
theorem key_hit_law {κ n : Nat} (key : Key κ) (attack : Attack κ n) :
    (attack.run (oracle RandomOracle.oracle key) ([], [])).map
      (fun out => out.trace.any (fun e => hitsKey key e.1)) =
    (attack.run RandomOracle.oracle []).map
      (fun out => out.trace.any (fun e => hitsKey key e.1)) := by
  have projection := congrArg (PMF.map
    (fun out => out.trace.any (fun e => hitsKey key e.1)))
      (rom_run_hash_projection key attack [] [])
  have hp : (attack.run (oracle RandomOracle.oracle key) ([], [])).map
      (fun out => out.trace.any (fun e => hitsKey key e.1)) =
    (attack.run (Program.adaptOracle (requestInput key) id RandomOracle.oracle) []).map
      (fun out => out.trace.any (fun e => hitsKey key e.1)) := by
    simpa only [PMF.map_comp, Program.mapState, Function.comp_def] using projection
  rw [hp, ← Program.stopBefore_run, ← Program.mapQueries_run_result]
  rw [stopped_domains_eq, Program.stopBefore_run]

/-- The bad-event probability in the actual ROM experiment equals that in
the independent-domain intermediate experiment. -/
theorem keyHitProbability_eq_separated {κ n : Nat} (attack : Attack κ n) :
    keyHitProbability attack = separatedKeyHitProbability attack := by
  have he : (romTranscript attack).map
      (fun pair => pair.2.trace.any (fun e => hitsKey pair.1 e.1)) =
    ((attack.run RandomOracle.oracle []).bind fun out =>
      (keygen κ).map (fun key => (key, out.trace))).map
      (fun pair => pair.2.any (fun e => hitsKey pair.1 e.1)) := by
    simp only [romTranscript, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc
      _ = (keygen κ).bind (fun key => (attack.run RandomOracle.oracle []).map
          (fun out => out.trace.any (fun e => hitsKey key e.1))) := by
        congr 1
        funext key
        exact key_hit_law key attack
      _ = _ := by
        simpa only [PMF.map, Function.comp_def] using
          PMF.bind_comm (keygen κ) (attack.run RandomOracle.oracle [])
            (fun key out => PMF.pure (out.trace.any (fun e => hitsKey key e.1)))
  have hp := congrArg (fun law => eventProb law (· = true)) he
  simpa only [keyHitProbability, separatedKeyHitProbability, eventProb_map,
    ← keyHit_iff_any] using hp

/-- Single-stage adaptive EUF-CMA security of the secret-prefix MAC in the
ROM. Hash and signing queries share one lazy random-oracle table. The attacker
may repeat queries and use arbitrary local coins; the forgery must be unsigned.
Length budgets constrain the domain but are not needed for this probability
bound. The final verification call is already included in the original game. -/
theorem rom_security {κ n hashLength messageLength qH qT : Nat}
    (messageLimit : Nat) (attack : Attack κ n)
    (budget : Budget hashLength messageLength attack qH qT) :
    successProbability messageLimit attack ≤
      qH * (Fintype.card (Key κ) : ℝ≥0∞)⁻¹ +
        (Fintype.card (Tag n) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ keyHitProbability attack + (Fintype.card (Tag n) : ℝ≥0∞)⁻¹ :=
      success_le_key_hit_add_guess messageLimit attack
    _ = separatedKeyHitProbability attack + (Fintype.card (Tag n) : ℝ≥0∞)⁻¹ := by
      rw [keyHitProbability_eq_separated]
    _ ≤ _ := add_le_add (separated_key_hit_bound attack budget) (le_refl _)

/-- The same concrete bound written in key and tag bit lengths. -/
theorem rom_security_bits {κ n hashLength messageLength qH qT : Nat}
    (messageLimit : Nat) (attack : Attack κ n)
    (budget : Budget hashLength messageLength attack qH qT) :
    successProbability messageLimit attack ≤
      qH * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  simpa [Key, Tag, Bits, Fintype.card_fun] using rom_security messageLimit attack budget

end Foundation.Symmetric.SecretPrefixMAC
