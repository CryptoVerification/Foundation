import Foundation.Constructions.ElGamal.PrimeOrderChooseValidation
import Foundation.Constructions.ElGamal.MachineSecurity

namespace ElGamal.PrimeOrderRepresentation

/-- Variant allowing an independently supplied exact normalizer. The concrete
normalizer below is used by the final theorem without an implementation argument. -/
theorem secureINDCPA_of_secureDDH_withNormalizer
    (N : RepresentedChooseNormalizer simulatorPrimitives)
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed))
    (hDDH : SecureOnWithin (representedDDHGoal sampling Domain embed)
      (representedDDHInterface sampling Domain embed
        simulatorPrimitives.instanceCode
        (fun n x => (simulatorPrimitives.elementCode n x).triple)).pptClass
      ((representedReduction sampling Domain embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling Domain embed)
      (representedINDCPAElementPPTClass sampling Domain embed
        simulatorPrimitives.instanceCode simulatorPrimitives.elementCode) F := by
  exact secureRepresentedINDCPA_of_secureRepresentedDDH_nativeMachinePPT
    sampling Domain embed simulatorPrimitives N F hDDH

/-- The concrete finite multiplication and normalization programs discharge
both implementation witnesses. DDH security remains the cryptographic premise. -/
theorem secureINDCPA_of_secureDDH
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed))
    (hDDH : SecureOnWithin (representedDDHGoal sampling Domain embed)
      (representedDDHInterface sampling Domain embed
        simulatorPrimitives.instanceCode
        (fun n x => (simulatorPrimitives.elementCode n x).triple)).pptClass
      ((representedReduction sampling Domain embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling Domain embed)
      (representedINDCPAElementPPTClass sampling Domain embed
        simulatorPrimitives.instanceCode simulatorPrimitives.elementCode) F := by
  exact secureINDCPA_of_secureDDH_withNormalizer chooseNormalizer F hDDH

end ElGamal.PrimeOrderRepresentation
