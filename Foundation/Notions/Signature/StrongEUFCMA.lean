import Foundation.Notions.Signature.EUFCMA

open scoped ENNReal

/-- Semantics for strong EUF-CMA (sEUF-CMA).

An implementation must generate keys, provide the public key and signing
capability, record each (message, signature) pair actually returned by signing,
verify the adversary's output, check that its pair was never returned, and
compute the normalized success measure. It tracks returned pairs rather than
only queried messages: randomized signing can return different signatures for
the same message. This interface does not prove those duties are fulfilled. -/
structure StrongEUFCMASemantics (M : Type → Type) where
  advantage : (n : Nat) → (scheme : SignatureScheme M) →
    EUFCMAAdversary M scheme → ℝ≥0∞

/-- Strong EUF-CMA uses the EUF-CMA adversary capability with pair-freshness semantics. -/
def StrongEUFCMA (M : Type → Type) (S : StrongEUFCMASemantics M) : CryptoGoal where
  Instance := fun _ => SignatureScheme M
  Adversary := fun _ scheme => EUFCMAAdversary M scheme
  advantage := fun n scheme A => S.advantage n scheme A
