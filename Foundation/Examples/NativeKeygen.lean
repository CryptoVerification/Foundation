import Foundation.Machine.NativeKeygen
import Foundation.Constructions.ElGamal.PrimeOrderNativeKeygen

namespace Foundation.Examples.NativeKeygen

/-- This small example tests the full operational distribution; it makes
no hardness claim about the group of order three modulo seven. -/
example (bits : List Bool) :
    Machine.outputMassFrom Machine.NativeKeygen.program
      (Machine.Configuration.initial (Machine.NativeKeygen.request 0 7 2 3)) bits =
      ((Foundation.Probability.uniform (Fin 3)).map (fun a =>
        Machine.frame (Machine.Binary.encode 3 (2^a.val % 7)) ++
          Machine.frame (Machine.Binary.encode 3 a.val))) bits :=
  Machine.NativeKeygen.outputMass_from_frame 0 7 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) bits

example : Machine.AlmostSureHalts Machine.NativeKeygen.program
    (Machine.NativeKeygen.request 0 7 2 3) :=
  Machine.NativeKeygen.almostSureHalts_from_frame 0 7 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : PolynomiallyBounded (fun n =>
    Machine.SavedFramedScalarInput.validBudget n
      (Machine.Binary.encode (n+3) 7) (Machine.Binary.encode (n+3) 2) + 1 +
        Machine.NativeKeygenSample.expectedBudget n) :=
  Machine.NativeKeygen.expectedBudget_polynomiallyBounded (fun _ => 7) (fun _ => 2)

end Foundation.Examples.NativeKeygen
