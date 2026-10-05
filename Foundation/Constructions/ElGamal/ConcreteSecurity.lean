import Foundation.Constructions.ElGamal.ConcreteReduction
import Foundation.Crypto.Semantics.Security.Reduction

namespace ElGamal

open Foundation.Probability

/-- Concrete DDH security against every adversary family transports to the
concrete finite ElGamal IND-CPA goal. The DDH assumption here is deliberately
strong: its class admits all adversary families, including adversaries with
unrestricted computation. This is a distribution-level transport lemma,
not the usual computational DDH hardness assumption. For the machine-class
result use `secureRepresentedINDCPA_of_secureRepresentedDDH_nativeMachinePPT`
in `MachineSecurity`. This secrecy theorem does not imply decryption
correctness; see `concreteInstance_correct` in `Correctness`. -/
theorem secureINDCPA_of_secureDDH_all
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (F : InstanceFamily (concreteINDCPAGoal sampling))
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics sampling))
      (AdversaryClass.all _)
      ((concreteReduction sampling).mapFamily F)) :
    SecureOnWithin (concreteINDCPAGoal sampling)
      (AdversaryClass.all _) F := by
  let R := concreteReduction sampling
  have hLoss : R.loss.PreservesNegligible := by
    change AdvantageBound.id.PreservesNegligible
    exact AdvantageBound.id_preservesNegligible
  exact R.secureOnWithin (AdversaryClass.all _)
    (AdversaryClass.all _) F
    (R.preservesAdmissibility_allTarget _) hLoss hDDH

end ElGamal
