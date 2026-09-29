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

example
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics bitSamplingFamily))
      (AdversaryClass.all _)
      ((concreteReduction bitSamplingFamily).mapFamily bitFamily)) :
    SecureOnWithin (concreteINDCPAGoal bitSamplingFamily)
      (AdversaryClass.all _) bitFamily :=
  secureINDCPA_of_secureDDH_all bitSamplingFamily bitFamily hDDH

/-- The execution-class theorem takes actual program and execution-cost
witnesses as inputs; it does not invent a cost for the DDH simulator. -/
example
    {MP : UniformAdversaryModel (concreteINDCPAGoal bitSamplingFamily)}
    {MQ : UniformAdversaryModel
      (DDH ProbComp (concreteDDHSemantics bitSamplingFamily))}
    (DP : MP.FiniteDescription) (DQ : MQ.FiniteDescription)
    {EP : MP.ExecutionSemantics} {EQ : MQ.ExecutionSemantics}
    (CP : EP.ExecutionCost) (CQ : EQ.ExecutionCost)
    {T : (concreteReduction bitSamplingFamily).ProgramTransformation MP MQ}
    (B : T.ResourceBound CP.toProgramResourceMeasure
      CQ.toProgramResourceMeasure)
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics bitSamplingFamily))
      (MQ.polynomialExecutionClass DQ CQ)
      ((concreteReduction bitSamplingFamily).mapFamily bitFamily)) :
    SecureOnWithin (concreteINDCPAGoal bitSamplingFamily)
      (MP.polynomialExecutionClass DP CP) bitFamily :=
  secureINDCPA_of_secureDDH bitSamplingFamily bitFamily DP DQ CP CQ B hDDH

end ElGamal.ConcreteSecurityExamples
