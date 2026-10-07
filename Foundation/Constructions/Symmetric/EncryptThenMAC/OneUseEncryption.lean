import Foundation.Constructions.Symmetric.EncryptThenMAC.Security

/-! Structural one-use behavior, independent of any secrecy assumption.
These contracts bound actual signing calls in the semantic reduction even
when the source makes arbitrarily many failed encryption requests. -/
namespace Foundation.Symmetric.EncryptThenMAC
open CryptoOracle

structure OneUseEncryption (E : Encryption) where
  exhausted : ∀ n, E.State n
  ciphertext : ∀ n, E.Key n → E.Message n → E.Ciphertext n
  first : ∀ n key message, E.encrypt n key (E.initial n) message =
    (exhausted n, some (ciphertext n key message))
  used : ∀ n key message, E.encrypt n key (exhausted n) message = (exhausted n, none)

namespace OneUseEncryption
variable {E : Encryption} (P : OneUseEncryption E) (M : MAC E.Ciphertext)
include P

theorem exhausted_queries (n : Nat) (key : E.Key n) (attack : IntegrityAttack E M n) :
    (reduceIntegrity E M key (P.exhausted n) attack).BoundedQueries 0 := by
  induction attack with
  | done candidate => exact .done _ _
  | query request next ih =>
      simpa only [reduceIntegrity, P.used] using ih none
  | coin next ih => exact .coin _ _ ih

theorem reduction_queries (n : Nat) (key : E.Key n) (attack : IntegrityAttack E M n) :
    (reduceIntegrity E M key (E.initial n) attack).BoundedQueries 1 := by
  induction attack with
  | done candidate => exact .done _ _
  | query request next ih =>
      rw [reduceIntegrity, P.first]
      exact .query _ _ 0 (fun tag => P.exhausted_queries M n key _)
  | coin next ih => exact .coin _ _ ih

end OneUseEncryption
end Foundation.Symmetric.EncryptThenMAC
