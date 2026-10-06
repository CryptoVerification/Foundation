import Foundation.Crypto.Meta.Extraction

namespace CryptoLogic

universe u v w a b

variable {L : Language.{a, b}} {S : Signature.{u, v, w} L}

/-- All explicitly supplied security hypotheses hold in the interpretation. -/
def Context.Valid (Γ : Context S) : Prop :=
  ∀ i : Fin Γ.length, (S.interpret (Γ[i]).object).Secure (Γ[i]).family

namespace Derivation

/-- Soundness follows from the extracted quantitative, resource-certified
reduction. It does not assume any common negligible bound for all attackers. -/
theorem sound {Γ : Context S} {X F} (d : Derivation S Γ X F)
    (hΓ : Γ.Valid) : (S.interpret X).Secure F := by
  apply d.extract.certificate.secure F
  rw [d.extract.family_eq]
  exact hΓ d.extract.index

/-- Only the selected hypothesis needs to hold. Unused context assumptions
remain visible but contribute nothing to this unary security derivation. -/
theorem sound_of_selected {Γ : Context S} {X F} (d : Derivation S Γ X F)
    (h : (S.interpret (Γ[d.extract.index]).object).Secure (Γ[d.extract.index]).family) :
    (S.interpret X).Secure F := by
  apply d.extract.certificate.secure F
  rw [d.extract.family_eq]
  exact h

end Derivation
end CryptoLogic
