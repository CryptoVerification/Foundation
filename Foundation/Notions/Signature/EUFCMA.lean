import Foundation.Core.Goal
import Foundation.Notions.Signature.Basic

open scoped ENNReal

/-- A signing-oracle adversary that outputs a message-signature forgery candidate.
It lives in `Type 1` to match signature-scheme instances in `CryptoGoal`. -/
structure EUFCMAAdversary (M : Type → Type) (scheme : SignatureScheme M) : Type 1 where
  forge : (scheme.Message → M scheme.Signature) → scheme.PublicKey →
    M (scheme.Message × scheme.Signature)

/-- A semantics for the normalized EUF-CMA success measure.

An implementation must generate keys, give the public key and signing access to
the adversary, record signing queries, verify the resulting pair, check that its
message was not queried, and compute the success probability or advantage.
This interface does not itself prove that an implementation does these things. -/
structure EUFCMASemantics (M : Type → Type) where
  advantage : (n : Nat) → (scheme : SignatureScheme M) →
    EUFCMAAdversary M scheme → ℝ≥0∞

/-- EUF-CMA as a goal over signature-scheme instances. -/
def EUFCMA (M : Type → Type) (S : EUFCMASemantics M) : CryptoGoal where
  Instance := fun _ => SignatureScheme M
  Adversary := fun _ scheme => EUFCMAAdversary M scheme
  advantage := fun n scheme A => S.advantage n scheme A
