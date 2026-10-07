import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitEncryption
import Foundation.Constructions.Symmetric.EncryptThenMAC.Security
import Foundation.Crypto.Semantics.Machine.FiniteRandomness

/-! Perfect privacy of the actual one-use encryption semantics, for arbitrary
finite adaptive attacks, including arbitrarily many exhausted-key requests. -/
namespace Foundation.Symmetric.EncryptThenMAC.OneBitEncryption
open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def xorEquiv (message : Bool) : Bool ≃ Bool where
  toFun := fun key => Bool.xor key message
  invFun := fun ciphertext => Bool.xor ciphertext message
  left_inv := by intro key; cases key <;> cases message <;> rfl
  right_inv := by intro ciphertext; cases ciphertext <;> cases message <;> rfl

theorem xor_uniform (message : Bool) :
    sampleBit.map (fun key => Bool.xor key message) = sampleBit :=
  Machine.uniform_map_equiv (xorEquiv message)

theorem oracle_unused (n : Nat) (key side : Bool) (request : Bool × Bool) :
    encryptionOracle scheme n key side false request =
      PMF.pure (true, some (Bool.xor key (selected side request))) := rfl

theorem oracle_used (n : Nat) (key side : Bool) (request : Bool × Bool) :
    encryptionOracle scheme n key side true request = PMF.pure (true, none) := rfl

/-- The exhaustion state remains exhausted and reveals no further key data. -/
theorem exhausted_result (n : Nat) (leftKey rightKey leftSide rightSide : Bool)
    (attack : EncryptionAttack scheme n) :
    (attack.run (encryptionOracle scheme n leftKey leftSide) true).map Outcome.result =
      (attack.run (encryptionOracle scheme n rightKey rightSide) true).map Outcome.result := by
  induction attack with
  | done result => simp [Program.run, PMF.pure_map]
  | query request next ih =>
      simp only [Program.run, oracle_used, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      exact ih none
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit

noncomputable def programGame (n : Nat) (side : Bool) (attack : EncryptionAttack scheme n) : PMF Bool :=
  sampleBit.bind fun key => (attack.run (encryptionOracle scheme n key side) false).map Outcome.result

/-- The first ciphertext is uniform; all later responses are failures. -/
theorem query_game (n : Nat) (side : Bool) (request : Bool × Bool)
    (next : Option Bool → EncryptionAttack scheme n) :
    programGame n side (.query request next) =
      sampleBit.bind (fun ciphertext =>
        ((next (some ciphertext)).run (encryptionOracle scheme n false false) true).map Outcome.result) := by
  simp only [programGame, Program.run, oracle_unused, PMF.pure_bind,
    PMF.map_comp, Function.comp_def]
  simp_rw [exhausted_result n _ false side false]
  have h := congrArg (fun p => p.bind (fun ciphertext =>
      ((next (some ciphertext)).run (encryptionOracle scheme n false false) true).map Outcome.result))
    (xor_uniform (selected side request))
  simpa only [PMF.bind_map, Function.comp_def] using h

/-- No query bound is needed beyond finiteness of the attack program. -/
theorem program_perfect (n : Nat) (attack : EncryptionAttack scheme n) :
    programGame n false attack = programGame n true attack := by
  induction attack with
  | done result => simp [programGame, Program.run, PMF.pure_map]
  | query request next ih => rw [query_game, query_game]
  | coin next ih =>
      unfold programGame
      simp only [Program.run, PMF.map_bind]
      conv_lhs => rw [PMF.bind_comm]
      conv_rhs => rw [PMF.bind_comm]
      congr 1
      funext bit
      exact ih bit

/-- Independent randomized selection of an attack also preserves exact secrecy. -/
theorem game_perfect (n : Nat) (attacks : PMF (EncryptionAttack scheme n)) :
    encryptionGame scheme n false attacks = encryptionGame scheme n true attacks := by
  unfold encryptionGame
  change (sampleBit.bind fun key => attacks.bind fun attack =>
      (attack.run (encryptionOracle scheme n key false) false).map Outcome.result) =
    (sampleBit.bind fun key => attacks.bind fun attack =>
      (attack.run (encryptionOracle scheme n key true) false).map Outcome.result)
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext attack
  exact program_perfect n attack

theorem advantage_zero (n : Nat) (attacks : PMF (EncryptionAttack scheme n)) :
    (encryptionGoal scheme).advantage n () attacks = 0 := by
  change probabilityGap (eventProb (encryptionGame scheme n false attacks) (· = true))
    (eventProb (encryptionGame scheme n true attacks) (· = true)) = 0
  rw [game_perfect]
  simp [probabilityGap]

/-- Authenticating the ciphertext with an independently sampled MAC key
preserves perfect privacy via the existing semantic reduction. -/
theorem privacy_perfect (M : MAC scheme.Ciphertext) (n : Nat) (attack : PrivacyAttack scheme M n) :
    privacyGame scheme M n false attack = privacyGame scheme M n true attack := by
  rw [privacyGame_eq, privacyGame_eq]
  exact game_perfect n _

end Foundation.Symmetric.EncryptThenMAC.OneBitEncryption
