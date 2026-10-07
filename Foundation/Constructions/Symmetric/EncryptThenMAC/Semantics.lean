import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Crypto.Semantics.Security.ThreeGames

/-! Stateful encrypt-then-MAC with independent encryption and authentication
keys. Encryption may fail (e.g. counter exhaustion); failures are not signed.
The games below permit adaptive encryption queries and local random coins.
Privacy is chosen-plaintext privacy, and integrity tests a final fresh
ciphertext/tag pair. Chosen-ciphertext privacy is not asserted here. -/
namespace Foundation.Symmetric.EncryptThenMAC

open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

structure Encryption where
  Key : Nat → Type
  State : Nat → Type
  Message : Nat → Type
  Ciphertext : Nat → Type
  keygen : ∀ n, ProbComp (Key n)
  initial : ∀ n, State n
  encrypt : ∀ n, Key n → State n → Message n → State n × Option (Ciphertext n)
  decrypt : ∀ n, Key n → Ciphertext n → Option (Message n)
  correctness : ∀ n key state message ciphertext,
    (encrypt n key state message).2 = some ciphertext →
      decrypt n key ciphertext = some message

structure MAC (Ciphertext : Nat → Type) where
  Key : Nat → Type
  Tag : Nat → Type
  keygen : ∀ n, ProbComp (Key n)
  sign : ∀ n, Key n → Ciphertext n → Tag n
  verify : ∀ n, Key n → Ciphertext n → Tag n → Bool
  correctness : ∀ n key ciphertext, verify n key ciphertext (sign n key ciphertext) = true

variable (E : Encryption) (M : MAC E.Ciphertext)

abbrev AuthCiphertext (n : Nat) := E.Ciphertext n × M.Tag n

-- Only successful ciphertexts are authenticated. The complete ciphertext,
-- including any nonce/counter in its type, is the MAC message.
def authenticate (n : Nat) (key : M.Key n) (ciphertext : Option (E.Ciphertext n)) :
    Option (AuthCiphertext E M n) := ciphertext.map fun c => (c, M.sign n key c)

def decrypt (n : Nat) (encryptionKey : E.Key n) (macKey : M.Key n)
    (ciphertext : AuthCiphertext E M n) : Option (E.Message n) :=
  if M.verify n macKey ciphertext.1 ciphertext.2 then E.decrypt n encryptionKey ciphertext.1 else none

theorem correctness (n : Nat) (encryptionKey : E.Key n) (macKey : M.Key n)
    (state : E.State n) (message : E.Message n) (ciphertext : E.Ciphertext n)
    (h : (E.encrypt n encryptionKey state message).2 = some ciphertext) :
    decrypt E M n encryptionKey macKey (ciphertext, M.sign n macKey ciphertext) = some message := by
  simp only [decrypt, M.correctness, ite_true]
  exact E.correctness n encryptionKey state message ciphertext h

def selected {Message : Type} (side : Bool) (request : Message × Message) : Message :=
  if side then request.2 else request.1

noncomputable def encryptionOracle (n : Nat) (key : E.Key n) (side : Bool) :
    Oracle (E.Message n × E.Message n) (Option (E.Ciphertext n)) (E.State n) :=
  fun state request => PMF.pure (E.encrypt n key state (selected side request))

noncomputable def privacyOracle (n : Nat) (key : E.Key n) (macKey : M.Key n) (side : Bool) :
    Oracle (E.Message n × E.Message n) (Option (AuthCiphertext E M n)) (E.State n) :=
  fun state request => let response := E.encrypt n key state (selected side request)
    PMF.pure (response.1, authenticate E M n macKey response.2)

abbrev PrivacyAttack (n : Nat) :=
  Program (E.Message n × E.Message n) (Option (AuthCiphertext E M n)) Bool
abbrev EncryptionAttack (n : Nat) :=
  Program (E.Message n × E.Message n) (Option (E.Ciphertext n)) Bool

def reducePrivacy {n : Nat} (macKey : M.Key n) : PrivacyAttack E M n → EncryptionAttack E n
  | .done result => .done result
  | .query request next => .query request (fun reply =>
      reducePrivacy macKey (next (authenticate E M n macKey reply)))
  | .coin next => .coin (fun bit => reducePrivacy macKey (next bit))

theorem privacy_simulation {n : Nat} (key : E.Key n) (macKey : M.Key n)
    (side : Bool) (state : E.State n) (attack : PrivacyAttack E M n) :
    ((reducePrivacy E M macKey attack).run (encryptionOracle E n key side) state).map Outcome.result =
      (attack.run (privacyOracle E M n key macKey side) state).map Outcome.result := by
  induction attack generalizing state with
  | done result => simp [reducePrivacy, Program.run, PMF.pure_map]
  | query request next ih =>
      simp only [reducePrivacy, Program.run, encryptionOracle, privacyOracle, PMF.pure_bind,
        PMF.map_comp, Function.comp_def]
      exact ih _ _
  | coin next ih =>
      simp only [reducePrivacy, Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

/-- The privacy simulator makes exactly one encryption query per source
query, including failed encryptions; local coins remain local coins. -/
theorem privacy_queries {n : Nat} {attack : PrivacyAttack E M n} {q : Nat}
    (h : attack.BoundedQueries q) (macKey : M.Key n) :
    (reducePrivacy E M macKey attack).BoundedQueries q := by
  induction h with
  | done result q => exact .done _ _
  | query request next q h ih => exact .query _ _ q (fun reply => ih _)
  | coin next q h ih => exact .coin _ q ih

end Foundation.Symmetric.EncryptThenMAC
