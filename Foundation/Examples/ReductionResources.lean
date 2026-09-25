import Foundation.Resource.Reduction
import Foundation.Asymptotics.AdvantageBound
import Foundation.Examples.Relations
import Foundation.Notions.PKE.Relations
import Foundation.Notions.Signature.Relations
import Foundation.Constructions.ElGamal.Relations

open scoped ENNReal

namespace Foundation.Examples.ReductionResources

def R : Reduction Foundation.Examples.Relations.A
    Foundation.Examples.Relations.B := Foundation.Examples.Relations.R₁

def F : InstanceFamily Foundation.Examples.Relations.A :=
  Foundation.Examples.Relations.FA

def attack : AdversaryFamily Foundation.Examples.Relations.A F :=
  fun _ => true

def transformedAttack : AdversaryFamily
    Foundation.Examples.Relations.B (R.mapFamily F) :=
  R.mapAdversaryFamily F attack

example (n : Nat) :
    advantageProfile Foundation.Examples.Relations.A F attack n ≤
      R.loss.eval n
        (advantageProfile Foundation.Examples.Relations.B
          (R.mapFamily F) transformedAttack n) :=
  R.advantageProfile_le F attack n

def sourceClass : AdversaryClass Foundation.Examples.Relations.A :=
  AdversaryClass.all _

def targetClass : AdversaryClass Foundation.Examples.Relations.B :=
  AdversaryClass.all _

theorem preservesDummyAdmissibility :
    R.PreservesAdmissibility sourceClass targetClass :=
  R.preservesAdmissibility_allTarget sourceClass

example : targetClass.admissible (R.mapFamily F) transformedAttack :=
  preservesDummyAdmissibility.preserves F attack trivial

example : AdvantageBound.id.PreservesNegligible :=
  AdvantageBound.id_preservesNegligible

example : (AdvantageBound.id.comp AdvantageBound.id).PreservesNegligible :=
  AdvantageBound.comp_preservesNegligible _ _
    AdvantageBound.id_preservesNegligible
    AdvantageBound.id_preservesNegligible

/-- Existing cryptographic reductions have identity advantage loss. These
checks make no claim about preservation of their adversary classes. -/
example : Foundation.Notions.PKE.RelationExamples.dummyReduction.loss.PreservesNegligible :=
  AdvantageBound.id_preservesNegligible

example : Foundation.Notions.Signature.RelationExamples.dummyReduction.loss.PreservesNegligible :=
  AdvantageBound.id_preservesNegligible

example : Foundation.Constructions.ElGamal.Relations.R.loss.PreservesNegligible :=
  AdvantageBound.id_preservesNegligible

end Foundation.Examples.ReductionResources
