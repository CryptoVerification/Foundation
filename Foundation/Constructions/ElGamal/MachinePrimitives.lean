import Foundation.Constructions.ElGamal.ConcreteReduction
import Foundation.Machine.PPT
import Foundation.Machine.Encoding

namespace ElGamal

open Foundation.Probability

/-- Explicit bit-machine obligations for the ElGamal arithmetic on one
concrete instance family. Each operation has one fixed finite code across
all security parameters and a worst-case polynomial bound in its total input
length. The parameter, element, and scalar codes have polynomial length in
the security parameter, so an exponential encoding is not hidden as free
machine input. The uniform scalar sampler must match the mathematical PMF exactly;
ordinary rejection sampling does not automatically provide such a bound.
These primitives alone do not construct the two-stage simulator compiler or
an encoding of the entire `ConcreteInstance` type. -/
structure MachinePrimitives
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (F : InstanceFamily (concreteINDCPAGoal sampling)) where
  parameterCode : Nat → List Bool
  parameterCode_polynomial :
    PolynomiallyBounded (fun n => (parameterCode n).length)
  elementCode : ∀ n, Machine.FiniteBitEncoding ((F n).params.Element)
  scalarCode : ∀ n, Machine.FiniteBitEncoding ((F n).params.Scalar)
  elementCodeLength : Nat → Nat
  elementCodeLength_polynomial : PolynomiallyBounded elementCodeLength
  elementCode_length_le : ∀ n (x : (F n).params.Element),
    ((elementCode n).encode x).length ≤ elementCodeLength n
  scalarCodeLength : Nat → Nat
  scalarCodeLength_polynomial : PolynomiallyBounded scalarCodeLength
  scalarCode_length_le : ∀ n (s : (F n).params.Scalar),
    ((scalarCode n).encode s).length ≤ scalarCodeLength n

  multiplyProgram : Machine.Program
  multiplyBudget : Nat → Nat
  multiplyBudget_polynomial : PolynomiallyBounded multiplyBudget
  multiplyHalts : ∀ input : List Bool,
    Machine.HaltsWithin multiplyProgram input (multiplyBudget input.length)
  multiply_correct : ∀ n (x y : (F n).params.Element),
    Machine.evalWithin multiplyProgram
      (Machine.encodeSecurityParameter n ++ Machine.frame (parameterCode n) ++
        Machine.frame ((elementCode n).encode x) ++
        Machine.frame ((elementCode n).encode y))
      (multiplyBudget (Machine.encodeSecurityParameter n ++
        Machine.frame (parameterCode n) ++
        Machine.frame ((elementCode n).encode x) ++
        Machine.frame ((elementCode n).encode y)).length) =
      PMF.pure (some ((elementCode n).encode ((F n).params.mul x y)))

  powerProgram : Machine.Program
  powerBudget : Nat → Nat
  powerBudget_polynomial : PolynomiallyBounded powerBudget
  powerHalts : ∀ input : List Bool,
    Machine.HaltsWithin powerProgram input (powerBudget input.length)
  power_correct : ∀ n (x : (F n).params.Element) (s : (F n).params.Scalar),
    Machine.evalWithin powerProgram
      (Machine.encodeSecurityParameter n ++ Machine.frame (parameterCode n) ++
        Machine.frame ((elementCode n).encode x) ++
        Machine.frame ((scalarCode n).encode s))
      (powerBudget (Machine.encodeSecurityParameter n ++
        Machine.frame (parameterCode n) ++
        Machine.frame ((elementCode n).encode x) ++
        Machine.frame ((scalarCode n).encode s)).length) =
      PMF.pure (some ((elementCode n).encode ((F n).params.power x s)))

  sampleProgram : Machine.Program
  sampleBudget : Nat → Nat
  sampleBudget_polynomial : PolynomiallyBounded sampleBudget
  sampleHalts : ∀ input : List Bool,
    Machine.HaltsWithin sampleProgram input (sampleBudget input.length)
  sample_correct : ∀ n,
    (Machine.evalWithin sampleProgram
      (Machine.encodeSecurityParameter n ++ Machine.frame (parameterCode n))
      (sampleBudget (Machine.encodeSecurityParameter n ++
        Machine.frame (parameterCode n)).length)).map
      (fun bits => bits.bind (scalarCode n).decode) =
      ((F n).algebra.sampling.sampleScalar).map some

namespace MachinePrimitives

/-- A finite DDH challenge code assembled from the existing element code.
This is a protocol encoding, not a machine implementation of group
arithmetic. -/
def tripleCode
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {F : InstanceFamily (concreteINDCPAGoal sampling)}
    (M : MachinePrimitives sampling F) (n : Nat) :
    Machine.FiniteBitEncoding
      ((F n).params.Element × (F n).params.Element ×
        (F n).params.Element) :=
  (M.elementCode n).triple

theorem tripleCode_length_le
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {F : InstanceFamily (concreteINDCPAGoal sampling)}
    (M : MachinePrimitives sampling F) (n : Nat)
    (triple : (F n).params.Element × (F n).params.Element ×
      (F n).params.Element) :
    ((M.tripleCode n).encode triple).length ≤
      5 * M.elementCodeLength n + 2 := by
  rcases triple with ⟨x, y, z⟩
  exact (M.elementCode n).triple_encode_length_le
    (M.elementCodeLength n) (M.elementCode_length_le n) x y z

theorem multiply_polynomialTime
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {F : InstanceFamily (concreteINDCPAGoal sampling)}
    (M : MachinePrimitives sampling F) :
    Machine.PolynomialTime M.multiplyProgram :=
  ⟨M.multiplyBudget, M.multiplyBudget_polynomial, M.multiplyHalts⟩

theorem power_polynomialTime
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {F : InstanceFamily (concreteINDCPAGoal sampling)}
    (M : MachinePrimitives sampling F) :
    Machine.PolynomialTime M.powerProgram :=
  ⟨M.powerBudget, M.powerBudget_polynomial, M.powerHalts⟩

theorem sample_polynomialTime
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {F : InstanceFamily (concreteINDCPAGoal sampling)}
    (M : MachinePrimitives sampling F) :
    Machine.PolynomialTime M.sampleProgram :=
  ⟨M.sampleBudget, M.sampleBudget_polynomial, M.sampleHalts⟩

end MachinePrimitives

end ElGamal
