import Foundation.Core.Goal
import Foundation.Notions.PKE.Basic

open scoped ENNReal

/-- A decryption capability. Its holder receives only decryption responses, not the secret key. -/
abbrev CCADecryptionOracle (M : Type → Type) (scheme : PKE M) : Type :=
  scheme.Ciphertext → M (Option scheme.Message)

/-- A two-stage adversary with decryption access in both stages and private state. -/
structure INDCCA2Adversary (M : Type → Type) (scheme : PKE M) where
  State : Type
  choose : CCADecryptionOracle M scheme → scheme.PublicKey →
    M (scheme.Message × scheme.Message × State)
  guess : CCADecryptionOracle M scheme → State → scheme.Ciphertext → M Bool

/-- A CCA2 experiment assigns a normalized advantage.

An implementation must handle key generation, challenge-bit sampling, encryption,
decryption interaction before and after the challenge, rejection of queries equal
to the challenge ciphertext after it is generated, the guess, and normalization.
The interface does not itself prove that an implementation obeys these rules. -/
structure INDCCA2Semantics (M : Type → Type) where
  advantage : (n : Nat) → (scheme : PKE M) → INDCCA2Adversary M scheme → ℝ≥0∞

/-- IND-CCA2 as a goal over the same PKE instances used by IND-CPA. -/
def INDCCA2 (M : Type → Type) (S : INDCCA2Semantics M) : CryptoGoal where
  Instance := fun _ => PKE M
  Adversary := fun _ scheme => INDCCA2Adversary M scheme
  advantage := fun n scheme A => S.advantage n scheme A
