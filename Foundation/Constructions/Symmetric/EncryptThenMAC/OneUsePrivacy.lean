import Foundation.Constructions.Symmetric.EncryptThenMAC.OneUseEncryption

/-! Scheme-independent perfect privacy for one-use encryption. Neither the
key, message, ciphertext, nor state type is restricted to bits. Only reachable
initial and exhausted states are constrained. These are semantic conditions,
not assumptions about machine execution costs. -/
namespace Foundation.Symmetric.EncryptThenMAC
open Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

structure OneUsePrivacy (E : Encryption) extends OneUseEncryption E where
  distribution : ∀ n, PMF (E.Ciphertext n)
  law : ∀ n message, (E.keygen n).map (fun key => ciphertext n key message) = distribution n

namespace OneUsePrivacy
variable {E : Encryption} (P : OneUsePrivacy E)
include P

noncomputable def failureOracle (n : Nat) :
    Oracle (E.Message n × E.Message n) (Option (E.Ciphertext n)) (E.State n) :=
  fun _ _ => PMF.pure (P.exhausted n, none)

theorem exhausted_result (n : Nat) (key : E.Key n) (side : Bool)
    (attack : EncryptionAttack E n) :
    (attack.run (encryptionOracle E n key side) (P.exhausted n)).map Outcome.result =
      (attack.run (P.failureOracle n) (P.exhausted n)).map Outcome.result := by
  induction attack with
  | done result => simp [Program.run, PMF.pure_map]
  | query request next ih =>
      simp only [Program.run, encryptionOracle, P.used, failureOracle, PMF.pure_bind,
        PMF.map_comp, Function.comp_def]
      exact ih none
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit

noncomputable def programGame (_P : OneUsePrivacy E) (n : Nat) (side : Bool) (attack : EncryptionAttack E n) : PMF Bool :=
  (E.keygen n).bind fun key =>
    (attack.run (encryptionOracle E n key side) (E.initial n)).map Outcome.result

theorem query_game (n : Nat) (side : Bool) (request : E.Message n × E.Message n)
    (next : Option (E.Ciphertext n) → EncryptionAttack E n) :
    P.programGame n side (.query request next) =
      (P.distribution n).bind (fun ciphertext =>
        ((next (some ciphertext)).run (P.failureOracle n) (P.exhausted n)).map Outcome.result) := by
  simp only [programGame, Program.run, encryptionOracle, P.first, PMF.pure_bind,
    PMF.map_comp, Function.comp_def]
  simp_rw [P.exhausted_result]
  have h := congrArg (fun p => p.bind (fun ciphertext =>
      ((next (some ciphertext)).run (P.failureOracle n) (P.exhausted n)).map Outcome.result))
    (P.law n (selected side request))
  simpa only [PMF.bind_map, Function.comp_def] using h

theorem program_perfect (n : Nat) (attack : EncryptionAttack E n) :
    P.programGame n false attack = P.programGame n true attack := by
  induction attack with
  | done result => simp [programGame, Program.run, PMF.pure_map]
  | query request next ih => rw [P.query_game, P.query_game]
  | coin next ih =>
      unfold programGame
      simp only [Program.run, PMF.map_bind]
      conv_lhs => rw [PMF.bind_comm]
      conv_rhs => rw [PMF.bind_comm]
      congr 1
      funext bit
      exact ih bit

theorem game_perfect (n : Nat) (attacks : PMF (EncryptionAttack E n)) :
    encryptionGame E n false attacks = encryptionGame E n true attacks := by
  unfold encryptionGame
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext attack
  exact P.program_perfect n attack

theorem advantage_zero (n : Nat) (attacks : PMF (EncryptionAttack E n)) :
    (encryptionGoal E).advantage n () attacks = 0 := by
  change probabilityGap (eventProb (encryptionGame E n false attacks) (· = true))
    (eventProb (encryptionGame E n true attacks) (· = true)) = 0
  rw [P.game_perfect]
  simp [probabilityGap]

theorem privacy_perfect (M : MAC E.Ciphertext) (n : Nat) (attack : PrivacyAttack E M n) :
    privacyGame E M n false attack = privacyGame E M n true attack := by
  rw [privacyGame_eq, privacyGame_eq]
  exact P.game_perfect n _

end OneUsePrivacy
end Foundation.Symmetric.EncryptThenMAC
