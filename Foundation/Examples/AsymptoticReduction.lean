import Foundation.Security.Reduction
import Foundation.Examples.Relations
import Foundation.Notions.PKE.Relations
import Foundation.Notions.Signature.Relations
import Foundation.Constructions.ElGamal.Relations

namespace Foundation.Examples.AsymptoticReduction

universe u v w

example (P : CryptoGoal.{u}) (F : InstanceFamily P)
    (A : AdversaryFamily P F) :
    (Reduction.id P).mapAdversaryFamily F A = A := by
  rfl

theorem identityTransport (P : CryptoGoal.{u}) (C : AdversaryClass P)
    (F : InstanceFamily P) (h : SecureOnWithin P C F) :
    SecureOnWithin P C F := by
  exact (Reduction.id P).secureOnWithin C C F
    (Reduction.id_preservesAdmissibility P C)
    AdvantageBound.id_preservesNegligible h

/-- Composition keeps the security implication directed from the final
target back to the original source. -/
example {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    (r₁ : Reduction P Q) (r₂ : Reduction Q S)
    (CP : AdversaryClass P) (CQ : AdversaryClass Q)
    (CS : AdversaryClass S) (F : InstanceFamily P)
    (h₁ : r₁.PreservesAdmissibility CP CQ)
    (h₂ : r₂.PreservesAdmissibility CQ CS)
    (hL₁ : r₁.loss.PreservesNegligible)
    (hL₂ : r₂.loss.PreservesNegligible)
    (hS : SecureOnWithin S CS ((r₁.comp r₂).mapFamily F)) :
    SecureOnWithin P CP F := by
  exact (r₁.comp r₂).secureOnWithin CP CS F
    (Reduction.comp_preservesAdmissibility r₁ r₂ CP CQ CS h₁ h₂)
    (AdvantageBound.comp_preservesNegligible r₁.loss r₂.loss hL₁ hL₂)
    hS

/-- A small, tight dummy reduction exercises the theorem without using a
cryptographic notion. -/
def dummyReduction : Reduction Foundation.Examples.Relations.A
    Foundation.Examples.Relations.B where
  mapInstance := fun _ => false
  reduce := fun _ _ => (0 : Fin 3)
  loss := AdvantageBound.id
  advantage_le := by
    intro n I A
    exact le_refl _

example (hQ : SecureOnWithin Foundation.Examples.Relations.B
    (AdversaryClass.all _) (dummyReduction.mapFamily Foundation.Examples.Relations.FA)) :
    SecureOnWithin Foundation.Examples.Relations.A
      (AdversaryClass.all _) Foundation.Examples.Relations.FA := by
  exact dummyReduction.secureOnWithin
    (AdversaryClass.all _) (AdversaryClass.all _)
    Foundation.Examples.Relations.FA
    (dummyReduction.preservesAdmissibility_allTarget (AdversaryClass.all _))
    AdvantageBound.id_preservesNegligible hQ

/-- The next three checks use unrestricted adversary classes. They state
transport implications and do not establish PPT security. -/
theorem cpaOfCca2
    (hCCA2 : SecureOnWithin
      (INDCCA2 Foundation.Notions.PKE.Examples.Plain
        Foundation.Notions.PKE.CCAExamples.dummySemantics)
      (AdversaryClass.all _)
      (Foundation.Notions.PKE.RelationExamples.dummyReduction.mapFamily
        Foundation.Notions.PKE.Examples.fixedSchemeFamily)) :
    SecureOnWithin
      (INDCPA Foundation.Notions.PKE.Examples.Plain
        Foundation.Notions.PKE.Examples.dummySemantics)
      (AdversaryClass.all _)
      Foundation.Notions.PKE.Examples.fixedSchemeFamily := by
  let R := Foundation.Notions.PKE.RelationExamples.dummyReduction
  exact R.secureOnWithin (AdversaryClass.all _) (AdversaryClass.all _)
    Foundation.Notions.PKE.Examples.fixedSchemeFamily
    (R.preservesAdmissibility_allTarget (AdversaryClass.all _))
    AdvantageBound.id_preservesNegligible hCCA2

theorem eufOfStrongEuf
    (hStrong : SecureOnWithin
      (StrongEUFCMA Foundation.Notions.Signature.Examples.Plain
        Foundation.Notions.Signature.RelationExamples.strongSemantics)
      (AdversaryClass.all _)
      (Foundation.Notions.Signature.RelationExamples.dummyReduction.mapFamily
        Foundation.Notions.Signature.RelationExamples.dummyFamily)) :
    SecureOnWithin
      (EUFCMA Foundation.Notions.Signature.Examples.Plain
        Foundation.Notions.Signature.Examples.dummySemantics)
      (AdversaryClass.all _)
      Foundation.Notions.Signature.RelationExamples.dummyFamily := by
  let R := Foundation.Notions.Signature.RelationExamples.dummyReduction
  exact R.secureOnWithin (AdversaryClass.all _) (AdversaryClass.all _)
    Foundation.Notions.Signature.RelationExamples.dummyFamily
    (R.preservesAdmissibility_allTarget (AdversaryClass.all _))
    AdvantageBound.id_preservesNegligible hStrong

theorem elGamalOfDDH
    (hDDH : SecureOnWithin
      (DDH Id Foundation.Constructions.ElGamal.Relations.Sddh)
      (AdversaryClass.all _)
      (Foundation.Constructions.ElGamal.Relations.R.mapFamily
        Foundation.Constructions.ElGamal.Relations.Ifam)) :
    SecureOnWithin
      (ElGamalINDCPA Id Foundation.Constructions.ElGamal.Relations.Sind)
      (AdversaryClass.all _)
      Foundation.Constructions.ElGamal.Relations.Ifam := by
  let R := Foundation.Constructions.ElGamal.Relations.R
  exact R.secureOnWithin (AdversaryClass.all _) (AdversaryClass.all _)
    Foundation.Constructions.ElGamal.Relations.Ifam
    (R.preservesAdmissibility_allTarget (AdversaryClass.all _))
    AdvantageBound.id_preservesNegligible hDDH

end Foundation.Examples.AsymptoticReduction
