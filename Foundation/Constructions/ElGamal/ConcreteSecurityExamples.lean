import Foundation.Constructions.ElGamal.ConcreteSecurity
import Foundation.Constructions.ElGamal.ConcreteReductionExamples

namespace ElGamal.ConcreteSecurityExamples

open Foundation.Probability
open ElGamal.ConcreteReductionExamples
open ElGamal.ConcreteExamples

/-- The DDH family in the security premise is exactly the family obtained by
mapping the concrete ElGamal instance family through the proved reduction. -/
example : (concreteReduction bitSamplingFamily).mapFamily bitFamily =
    (fun _ => bitParams) := rfl

/-- This implication checks the unrestricted transport API. It supplies no
DDH hardness proof for the two-element toy family. -/
example
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics bitSamplingFamily))
      (AdversaryClass.all _)
      ((concreteReduction bitSamplingFamily).mapFamily bitFamily)) :
    SecureOnWithin (concreteINDCPAGoal bitSamplingFamily)
      (AdversaryClass.all _) bitFamily :=
  secureINDCPA_of_secureDDH_all bitSamplingFamily bitFamily hDDH

end ElGamal.ConcreteSecurityExamples
