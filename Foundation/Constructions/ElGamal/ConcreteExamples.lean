import Foundation.Constructions.ElGamal.Concrete

namespace ElGamal.ConcreteExamples

open Foundation.Probability

def bitParams : DDHParameters where
  Element := Bool
  Scalar := Bool
  generator := true
  power := fun g x => g && x
  mulScalar := fun x y => x && y
  mul := fun m t => Bool.xor m t

def bitSampling : DDHFiniteSampling bitParams where
  scalarFintype := by change Fintype Bool; infer_instance
  scalarNonempty := by change Nonempty Bool; infer_instance

def bitAlgebra : FiniteAlgebra bitParams where
  sampling := bitSampling
  powerEquiv := Equiv.refl Bool
  powerEquiv_apply := by intro x; cases x <;> rfl
  mulLeftEquiv := fun m =>
    { toFun := fun t => Bool.xor m t
      invFun := fun t => Bool.xor m t
      left_inv := by intro t; cases m <;> cases t <;> rfl
      right_inv := by intro t; cases m <;> cases t <;> rfl }
  mulLeftEquiv_apply := by intro m t; rfl
  power_mul := by intro x y; cases x <;> cases y <;> rfl

/-- Deliberately failing decryptor for the advantage-equality API check.
This example does not establish a correct encryption scheme; the actual
group decryptor and correctness examples are in `CorrectnessExamples`. -/
def bitDecrypt : bitParams.Scalar →
    (bitParams.Element × bitParams.Element) → Option bitParams.Element :=
  fun _ _ => none

example (A : INDCPAAdversary ProbComp
    (concreteInstance bitParams bitAlgebra bitDecrypt).scheme) :
    ddhAdvantage bitParams bitAlgebra.sampling
      (ddhAdversaryOfINDCPA sampleBit
        (concreteInstance bitParams bitAlgebra bitDecrypt) A) =
    indCPAAdvantage (concreteInstance bitParams bitAlgebra bitDecrypt).scheme A :=
  concrete_advantage_eq bitParams bitAlgebra bitDecrypt A

end ElGamal.ConcreteExamples
