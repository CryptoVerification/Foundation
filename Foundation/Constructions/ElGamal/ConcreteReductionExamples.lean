import Foundation.Constructions.ElGamal.ConcreteReduction
import Foundation.Constructions.ElGamal.ConcreteExamples

namespace ElGamal.ConcreteReductionExamples

open Foundation.Probability
open ElGamal.ConcreteExamples

noncomputable def bitSamplingFamily (_n : Nat) (params : DDHParameters) :
    Option (DDHFiniteSampling params) := by
  classical
  exact if h : params = bitParams then some (h.symm ▸ bitSampling) else none

noncomputable def bitInstance (n : Nat) : ConcreteInstance bitSamplingFamily n where
  params := bitParams
  algebra := bitAlgebra
  decrypt := bitDecrypt
  sampling_eq := by simp [bitSamplingFamily, bitAlgebra]

noncomputable def bitFamily : InstanceFamily (concreteINDCPAGoal bitSamplingFamily) :=
  bitInstance

example : (concreteReduction bitSamplingFamily).loss = AdvantageBound.id := rfl

example : (concreteReduction bitSamplingFamily).mapFamily bitFamily =
    (fun _ => bitParams) := rfl

example (n : Nat)
    (A : INDCPAAdversary ProbComp (bitInstance n).toElGamalInstance.scheme) :
    concreteINDCPASemantics.advantage n (bitInstance n).toElGamalInstance.scheme A =
      (concreteDDHSemantics bitSamplingFamily).advantage n bitParams
        (ddhAdversaryOfINDCPA sampleBit (bitInstance n).toElGamalInstance A) :=
  concreteCompatibility_eq bitSamplingFamily n (bitInstance n) A

end ElGamal.ConcreteReductionExamples
