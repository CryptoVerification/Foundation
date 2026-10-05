import Foundation.Constructions.ElGamal.PrimeOrderScalarSampler
import Foundation.Machine.NativeEncryption

namespace ElGamal.PrimeOrderRepresentation

open Foundation.Probability
open scoped ENNReal

/-- The full native encryption request uses the existing parameter and
both element codecs. This is serialization, not an extra machine primitive. -/
noncomputable def encryptionRequest (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) : List Bool :=
  Machine.encodeSecurityParameter n ++ Machine.frame
    ((instanceCode n).encode x ++ (elementCode n x).encode pk ++ (elementCode n x).encode m)

private theorem encryptionRequest_eq (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) :
    encryptionRequest n x pk m = Machine.NativeEncryption.request n
      x.down.modulus x.down.generator.val.val x.down.scalarOrder pk.val.val.val m.val.val.val := rfl

/-- Rejection sampling stops with probability one. This certificate does
not assert a common worst-case time bound for every random branch. -/
theorem nativeEncryption_almostSureHalts (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) :
    Machine.AlmostSureHalts Machine.NativeEncryption.program (encryptionRequest n x pk m) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  rw [encryptionRequest_eq]
  exact Machine.NativeEncryption.almostSureHalts_from_frame n x.down.modulus
    x.down.generator.val.val pk.val.val.val m.val.val.val x.down.scalarOrder
    x.down.modulus_prime.one_lt x.down.modulus_lt (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

private theorem power_residue {n : Nat} (C : PrimeOrderParameters n)
    (a : C.parameters.Element) (r : C.parameters.Scalar) :
    (C.parameters.power a r).val.val.val = a.val.val.val^r.val % C.modulus := by
  let : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  have cast : ((a.val.val.val^r.val : Nat) : ZMod C.modulus) = a.val.val^r.val := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  change (a.val.val^r.val).val = _
  rw [← cast, ZMod.val_natCast]

/-- Separate the mathematical codec equality from the large compiled code,
so the kernel only checks the scalar-to-ciphertext map once. -/
private theorem encoded_encryption (n : Nat) (x : Domain n) [NeZero x.down.scalarOrder]
    (pk m : (embed n x).params.Element) :
    ((uniform (Fin x.down.scalarOrder)).map (fun r =>
      Machine.frame (Machine.Binary.encode (n+3)
        (x.down.generator.val.val^r.val % x.down.modulus)) ++
      Machine.frame (Machine.Binary.encode (n+3)
        (m.val.val.val*(pk.val.val.val^r.val % x.down.modulus) % x.down.modulus)))) =
    ((embed n x).toElGamalInstance.scheme.encrypt pk m).map
      (fun ciphertext : (embed n x).params.Element × (embed n x).params.Element =>
        Machine.frame ((elementCode n x).encode ciphertext.1) ++
          Machine.frame ((elementCode n x).encode ciphertext.2)) := by
  have ideal : (embed n x).algebra.sampling.sampleScalar = uniform (Fin x.down.scalarOrder) := by
    change @uniform (Fin x.down.scalarOrder)
      (embed n x).algebra.sampling.scalarFintype
      (embed n x).algebra.sampling.scalarNonempty = _
    rw [show (embed n x).algebra.sampling.scalarFintype =
      inferInstanceAs (Fintype (Fin x.down.scalarOrder)) from Subsingleton.elim _ _]
    rfl
  change _ = ((embed n x).algebra.sampling.sampleScalar.map (fun r =>
    ((embed n x).params.power (embed n x).params.generator r,
      (embed n x).params.mul m ((embed n x).params.power pk r)))).map
        (fun ciphertext : (embed n x).params.Element × (embed n x).params.Element =>
          Machine.frame ((elementCode n x).encode ciphertext.1) ++
            Machine.frame ((elementCode n x).encode ciphertext.2))
  let choices : PMF (embed n x).params.Scalar := uniform (Fin x.down.scalarOrder)
  have choicesEq : (embed n x).algebra.sampling.sampleScalar = choices := ideal
  rw [choicesEq, PMF.map_comp]
  have encoded : ((uniform (Fin x.down.scalarOrder)).map (fun r =>
      Machine.frame (Machine.Binary.encode (n+3)
        (x.down.generator.val.val^r.val % x.down.modulus)) ++
      Machine.frame (Machine.Binary.encode (n+3)
        (m.val.val.val*(pk.val.val.val^r.val % x.down.modulus) % x.down.modulus)))) =
      choices.map (fun r =>
        Machine.frame ((elementCode n x).encode ((embed n x).params.power (embed n x).params.generator r)) ++
          Machine.frame ((elementCode n x).encode
            ((embed n x).params.mul m ((embed n x).params.power pk r)))) := by
    apply congrArg (fun f : Fin x.down.scalarOrder → List Bool => (uniform (Fin x.down.scalarOrder)).map f)
    funext r
    change _ = Machine.frame (x.down.elementCode.encode
      (x.down.parameters.power x.down.parameters.generator r)) ++
        Machine.frame (x.down.elementCode.encode
          (x.down.parameters.mul m (x.down.parameters.power pk r)))
    change x.down.parameters.Element at pk m
    have first := x.down.elementCode_power x.down.parameters.generator r
    have second := x.down.elementCode_mul m (x.down.parameters.power pk r)
    have shared := power_residue x.down pk r
    rw [first, second, shared]
    rfl
  exact encoded

/-- The actual finite encryption code realizes the existing ElGamal
`scheme.encrypt` distribution with the existing ciphertext element codecs.
Every retry and the final caller halt remain in the execution semantics. -/
theorem nativeEncryption_exact (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) :
    Machine.evalLimit Machine.NativeEncryption.program (encryptionRequest n x pk m)
      (nativeEncryption_almostSureHalts n x pk m) =
    ((embed n x).toElGamalInstance.scheme.encrypt pk m).map
      (fun ciphertext : (embed n x).params.Element × (embed n x).params.Element =>
        Machine.frame ((elementCode n x).encode ciphertext.1) ++
          Machine.frame ((elementCode n x).encode ciphertext.2)) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  let : NeZero x.down.scalarOrder := ⟨x.down.scalarOrder_prime.ne_zero⟩
  have law := Machine.NativeEncryption.evalLimit_from_frame n x.down.modulus
    x.down.generator.val.val pk.val.val.val m.val.val.val x.down.scalarOrder
    x.down.modulus_prime.one_lt x.down.modulus_lt (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)
  exact law.trans (encoded_encryption n x pk m)

noncomputable def encryptionExpectedBudget (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) : Nat :=
  Machine.SavedFramedScalarInput.validBudget n (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val ++
      Machine.Binary.encode (n+3) pk.val.val.val ++ Machine.Binary.encode (n+3) m.val.val.val) + 1 +
    Machine.NativeEncryptionSample.expectedBudget n

theorem nativeEncryption_expectedSteps (n : Nat) (x : Domain n)
    (pk m : (embed n x).params.Element) :
    Machine.expectedSteps Machine.NativeEncryption.program (encryptionRequest n x pk m) ≤
      (encryptionExpectedBudget n x pk m : ℝ≥0∞) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  rw [encryptionRequest_eq]
  exact Machine.NativeEncryption.expectedSteps_from_frame n x.down.modulus
    x.down.generator.val.val pk.val.val.val m.val.val.val x.down.scalarOrder
    x.down.modulus_prime.one_lt x.down.modulus_lt (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

theorem encryptionExpectedBudget_polynomiallyBounded (F : (n : Nat) → Domain n)
    (pk m : (n : Nat) → (embed n (F n)).params.Element) :
    PolynomiallyBounded (fun n => encryptionExpectedBudget n (F n) (pk n) (m n)) :=
  Machine.NativeEncryption.expectedBudget_polynomiallyBounded
    (fun n => (F n).down.modulus) (fun n => (F n).down.generator.val.val)
    (fun n => (pk n).val.val.val) (fun n => (m n).val.val.val)

end ElGamal.PrimeOrderRepresentation
