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

/-- Exactly the represented operations used by the native ElGamal-to-DDH
simulator. Multiplication has one fixed finite code, an all-input all-branch
polynomial stopping bound, and exact correctness on represented operands.
Scalar sampling and exponentiation are separate obligations for key generation
and encryption; the simulator does not invoke them. -/
structure RepresentedSimulatorPrimitives
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n) where
  instanceCode : ∀ n, Machine.FiniteBitEncoding (X n)
  instanceCodeLength : Nat → Nat
  instanceCodeLength_polynomial : PolynomiallyBounded instanceCodeLength
  instanceCode_length_le : ∀ n (x : X n),
    ((instanceCode n).encode x).length ≤ instanceCodeLength n
  elementCode : ∀ n (x : X n),
    Machine.FiniteBitEncoding ((embed n x).params.Element)
  elementCodeLength : Nat → Nat
  elementCodeLength_polynomial : PolynomiallyBounded elementCodeLength
  elementCode_length_le : ∀ n (x : X n) (a : (embed n x).params.Element),
    ((elementCode n x).encode a).length ≤ elementCodeLength n
  multiplyProgram : Machine.Program
  multiplyBudget : Nat → Nat
  multiplyBudget_polynomial : PolynomiallyBounded multiplyBudget
  multiplyHalts : ∀ input : List Bool,
    Machine.HaltsWithin multiplyProgram input (multiplyBudget input.length)
  multiply_correct : ∀ n (x : X n) (a b : (embed n x).params.Element),
    Machine.evalWithin multiplyProgram
      (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b))
      (multiplyBudget (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b)).length) =
      PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b)))

/-- Arithmetic implementation certificates on a finitely represented
instance domain. The three finite programs and their budgets are fixed
before any instance family is chosen. They receive only the encoded current
instance and operands; correctness holds for every represented instance.
Thus one compiler may refer to these programs without inspecting `F`.
This does not supply the protocol wrapper, tape preparation, or an efficient
algorithm for converting an arbitrary mathematical instance into its code. -/
structure RepresentedMachinePrimitives
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n) where
  instanceCode : ∀ n, Machine.FiniteBitEncoding (X n)
  instanceCodeLength : Nat → Nat
  instanceCodeLength_polynomial : PolynomiallyBounded instanceCodeLength
  instanceCode_length_le : ∀ n (x : X n),
    ((instanceCode n).encode x).length ≤ instanceCodeLength n
  elementCode : ∀ n (x : X n),
    Machine.FiniteBitEncoding ((embed n x).params.Element)
  scalarCode : ∀ n (x : X n),
    Machine.FiniteBitEncoding ((embed n x).params.Scalar)
  elementCodeLength : Nat → Nat
  elementCodeLength_polynomial : PolynomiallyBounded elementCodeLength
  elementCode_length_le : ∀ n (x : X n) (a : (embed n x).params.Element),
    ((elementCode n x).encode a).length ≤ elementCodeLength n
  scalarCodeLength : Nat → Nat
  scalarCodeLength_polynomial : PolynomiallyBounded scalarCodeLength
  scalarCode_length_le : ∀ n (x : X n) (s : (embed n x).params.Scalar),
    ((scalarCode n x).encode s).length ≤ scalarCodeLength n

  multiplyProgram : Machine.Program
  multiplyBudget : Nat → Nat
  multiplyBudget_polynomial : PolynomiallyBounded multiplyBudget
  multiplyHalts : ∀ input : List Bool,
    Machine.HaltsWithin multiplyProgram input (multiplyBudget input.length)
  multiply_correct : ∀ n (x : X n) (a b : (embed n x).params.Element),
    Machine.evalWithin multiplyProgram
      (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b))
      (multiplyBudget (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b)).length) =
      PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b)))

  powerProgram : Machine.Program
  powerBudget : Nat → Nat
  powerBudget_polynomial : PolynomiallyBounded powerBudget
  powerHalts : ∀ input : List Bool,
    Machine.HaltsWithin powerProgram input (powerBudget input.length)
  power_correct : ∀ n (x : X n) (a : (embed n x).params.Element)
      (s : (embed n x).params.Scalar),
    Machine.evalWithin powerProgram
      (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((scalarCode n x).encode s))
      (powerBudget (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((scalarCode n x).encode s)).length) =
      PMF.pure (some ((elementCode n x).encode ((embed n x).params.power a s)))

  sampleProgram : Machine.Program
  sampleBudget : Nat → Nat
  sampleBudget_polynomial : PolynomiallyBounded sampleBudget
  sampleHalts : ∀ input : List Bool,
    Machine.HaltsWithin sampleProgram input (sampleBudget input.length)
  sample_correct : ∀ n (x : X n),
    (Machine.evalWithin sampleProgram
      (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x))
      (sampleBudget (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x)).length)).map
      (fun bits => bits.bind (scalarCode n x).decode) =
      ((embed n x).algebra.sampling.sampleScalar).map some

namespace RepresentedMachinePrimitives

/-- Forget the power and scalar-sampler certificates. The emitted simulator
uses exactly these retained codes and codecs; no new algorithm is selected. -/
def toSimulatorPrimitives
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
    (M : RepresentedMachinePrimitives sampling X embed) :
    RepresentedSimulatorPrimitives sampling X embed where
  instanceCode := M.instanceCode
  instanceCodeLength := M.instanceCodeLength
  instanceCodeLength_polynomial := M.instanceCodeLength_polynomial
  instanceCode_length_le := M.instanceCode_length_le
  elementCode := M.elementCode
  elementCodeLength := M.elementCodeLength
  elementCodeLength_polynomial := M.elementCodeLength_polynomial
  elementCode_length_le := M.elementCode_length_le
  multiplyProgram := M.multiplyProgram
  multiplyBudget := M.multiplyBudget
  multiplyBudget_polynomial := M.multiplyBudget_polynomial
  multiplyHalts := M.multiplyHalts
  multiply_correct := M.multiply_correct

/-- Specialize correctness and input-length bounds to a chosen family while
retaining exactly the same finite operation programs. No program is selected
from the family and no classical choice is used. -/
def forFamily
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    (M : RepresentedMachinePrimitives sampling X embed)
    (F : (n : Nat) → X n) :
    MachinePrimitives sampling (fun n => embed n (F n)) where
  parameterCode := fun n => (M.instanceCode n).encode (F n)
  parameterCode_polynomial := PolynomiallyBounded.mono
    (fun n => M.instanceCode_length_le n (F n)) M.instanceCodeLength_polynomial
  elementCode := fun n => M.elementCode n (F n)
  scalarCode := fun n => M.scalarCode n (F n)
  elementCodeLength := M.elementCodeLength
  elementCodeLength_polynomial := M.elementCodeLength_polynomial
  elementCode_length_le := fun n => M.elementCode_length_le n (F n)
  scalarCodeLength := M.scalarCodeLength
  scalarCodeLength_polynomial := M.scalarCodeLength_polynomial
  scalarCode_length_le := fun n => M.scalarCode_length_le n (F n)
  multiplyProgram := M.multiplyProgram
  multiplyBudget := M.multiplyBudget
  multiplyBudget_polynomial := M.multiplyBudget_polynomial
  multiplyHalts := M.multiplyHalts
  multiply_correct := fun n => M.multiply_correct n (F n)
  powerProgram := M.powerProgram
  powerBudget := M.powerBudget
  powerBudget_polynomial := M.powerBudget_polynomial
  powerHalts := M.powerHalts
  power_correct := fun n => M.power_correct n (F n)
  sampleProgram := M.sampleProgram
  sampleBudget := M.sampleBudget
  sampleBudget_polynomial := M.sampleBudget_polynomial
  sampleHalts := M.sampleHalts
  sample_correct := fun n => M.sample_correct n (F n)

end RepresentedMachinePrimitives

end ElGamal
