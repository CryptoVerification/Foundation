import Foundation.Constructions.ElGamal.Concrete
import Foundation.Constructions.ElGamal.ToDDHReduction

open Foundation.Probability

namespace ElGamal

/-- An ElGamal instance whose operations are the concrete finite construction
and whose scalar sampler agrees with the DDH semantics at this parameter.
The original `ElGamalInstance` also permits arbitrary constructions, so this
restriction is essential to a theorem derived from probability games. -/
structure ConcreteInstance
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params))
    (n : Nat) where
  params : DDHParameters
  algebra : FiniteAlgebra params
  decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element
  sampling_eq : sampling n params = some algebra.sampling

namespace ConcreteInstance

noncomputable def toElGamalInstance
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {n : Nat} (I : ConcreteInstance sampling n) : ElGamalInstance ProbComp :=
  concreteInstance I.params I.algebra I.decrypt

end ConcreteInstance

/-- IND-CPA restricted to the concrete finite ElGamal constructions. -/
noncomputable def concreteINDCPAGoal
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)) :
    CryptoGoal :=
  (INDCPA ProbComp concreteINDCPASemantics).reindex
    (ConcreteInstance sampling)
    (fun _ I => I.toElGamalInstance.scheme)

/-- Concrete compatibility is an equality, derived from the real-branch
simulation and random-branch masking proof, for every concrete instance. -/
theorem concreteCompatibility_eq
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params))
    (n : Nat) (I : ConcreteInstance sampling n)
    (A : INDCPAAdversary ProbComp I.toElGamalInstance.scheme) :
    concreteINDCPASemantics.advantage n I.toElGamalInstance.scheme A =
      (concreteDDHSemantics sampling).advantage n I.params
        (ddhAdversaryOfINDCPA sampleBit I.toElGamalInstance A) := by
  change indCPAAdvantage I.toElGamalInstance.scheme A = _
  simp only [concreteDDHSemantics, I.sampling_eq]
  exact (concrete_advantage_eq I.params I.algebra I.decrypt A).symm

/-- The existing ElGamal simulator and identity loss, now supplied with a
proved concrete compatibility relation on the valid instance domain. -/
noncomputable def concreteReduction
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)) :
    Reduction (concreteINDCPAGoal sampling)
      (DDH ProbComp (concreteDDHSemantics sampling)) :=
  elGamalINDCPA_to_DDH_reductionOn ProbComp sampleBit concreteINDCPASemantics
    (concreteDDHSemantics sampling) (ConcreteInstance sampling)
    (fun _ I => I.toElGamalInstance)
    (by
      intro n I A
      exact le_of_eq (concreteCompatibility_eq sampling n I A))

end ElGamal
