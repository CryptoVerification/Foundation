import Foundation.Constructions.ElGamal.ConcreteReduction
import Foundation.Resource.PolynomialExecution
import Foundation.Resource.ProgramReduction
import Foundation.Security.Reduction

namespace ElGamal

open Foundation.Probability

/-- Concrete DDH security against every adversary family transports to the
concrete finite ElGamal IND-CPA goal. The DDH assumption here is deliberately
strong: its class admits all adversary families. -/
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

/-- Conditional security transport for families realized by finitely
describable programs with polynomial validated execution length. `T` and `B`
are explicit program-transformation and execution-cost witnesses for the
concrete reduction; no execution cost of the simulator is assumed implicitly.
The same transformed program supplies the target realization and resource
witness through `B.preservesAdmissibility`. -/
theorem secureINDCPA_of_secureDDH
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (F : InstanceFamily (concreteINDCPAGoal sampling))
    {MP : UniformAdversaryModel (concreteINDCPAGoal sampling)}
    {MQ : UniformAdversaryModel
      (DDH ProbComp (concreteDDHSemantics sampling))}
    (DP : MP.FiniteDescription) (DQ : MQ.FiniteDescription)
    {EP : MP.ExecutionSemantics} {EQ : MQ.ExecutionSemantics}
    (CP : EP.ExecutionCost) (CQ : EQ.ExecutionCost)
    {T : (concreteReduction sampling).ProgramTransformation MP MQ}
    (B : T.ResourceBound CP.toProgramResourceMeasure
      CQ.toProgramResourceMeasure)
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics sampling))
      (MQ.polynomialExecutionClass DQ CQ)
      ((concreteReduction sampling).mapFamily F)) :
    SecureOnWithin (concreteINDCPAGoal sampling)
      (MP.polynomialExecutionClass DP CP) F := by
  let R := concreteReduction sampling
  have hLoss : R.loss.PreservesNegligible := by
    change AdvantageBound.id.PreservesNegligible
    exact AdvantageBound.id_preservesNegligible
  exact R.secureOnWithin
    (MP.polynomialExecutionClass DP CP)
    (MQ.polynomialExecutionClass DQ CQ) F
    B.preservesAdmissibility hLoss hDDH

end ElGamal
