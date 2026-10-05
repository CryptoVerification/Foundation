import Foundation.Constructions.ElGamal.PrimeOrderNativeEncryption

namespace Foundation.Examples.NativeEncryption

open scoped ENNReal

/-- A small operational example checks exact encryption, without asserting
cryptographic hardness of this finite parameter choice. -/
example (bits : List Bool) :
    Machine.outputMassFrom Machine.NativeEncryption.program
      (Machine.Configuration.initial (Machine.NativeEncryption.request 0 7 2 3 4 2)) bits =
      ((Foundation.Probability.uniform (Fin 3)).map (fun a =>
        Machine.frame (Machine.Binary.encode 3 (2^a.val % 7)) ++
          Machine.frame (Machine.Binary.encode 3 (2*(4^a.val % 7) % 7)))) bits :=
  Machine.NativeEncryption.outputMass_from_frame 0 7 2 4 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) bits

example : Machine.AlmostSureHalts Machine.NativeEncryption.program
    (Machine.NativeEncryption.request 0 7 2 3 4 2) :=
  Machine.NativeEncryption.almostSureHalts_from_frame 0 7 2 4 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

example : Machine.expectedSteps Machine.NativeEncryption.program
    (Machine.NativeEncryption.request 0 7 2 3 4 2) ≤
      ((Machine.SavedFramedScalarInput.validBudget 0 (Machine.Binary.encode 3 7)
        (Machine.Binary.encode 3 2 ++ Machine.Binary.encode 3 4 ++
          Machine.Binary.encode 3 2) + 1 +
        Machine.NativeEncryptionSample.expectedBudget 0 : Nat) : ℝ≥0∞) :=
  Machine.NativeEncryption.expectedSteps_from_frame 0 7 2 4 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

example : PolynomiallyBounded (fun n =>
    Machine.SavedFramedScalarInput.validBudget n
      (Machine.Binary.encode (n+3) 7)
      (Machine.Binary.encode (n+3) 2 ++ Machine.Binary.encode (n+3) 4 ++
        Machine.Binary.encode (n+3) 2) + 1 +
      Machine.NativeEncryptionSample.expectedBudget n) :=
  Machine.NativeEncryption.expectedBudget_polynomiallyBounded
    (fun _ => 7) (fun _ => 2) (fun _ => 4) (fun _ => 2)

/-- The machine distribution is the existing cryptographic construction,
not only an independently defined arithmetic specification. -/
example (n : Nat) (x : ElGamal.PrimeOrderRepresentation.Domain n)
    (pk m : (ElGamal.PrimeOrderRepresentation.embed n x).params.Element) :
    Machine.evalLimit Machine.NativeEncryption.program
      (ElGamal.PrimeOrderRepresentation.encryptionRequest n x pk m)
      (ElGamal.PrimeOrderRepresentation.nativeEncryption_almostSureHalts n x pk m) =
      ((ElGamal.PrimeOrderRepresentation.embed n x).toElGamalInstance.scheme.encrypt pk m).map
        (fun ciphertext =>
          Machine.frame ((ElGamal.PrimeOrderRepresentation.elementCode n x).encode ciphertext.1) ++
            Machine.frame ((ElGamal.PrimeOrderRepresentation.elementCode n x).encode ciphertext.2)) :=
  ElGamal.PrimeOrderRepresentation.nativeEncryption_exact n x pk m

end Foundation.Examples.NativeEncryption
