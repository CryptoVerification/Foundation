import Foundation.Constructions.ElGamal.PrimeOrderScalarSampler
import Foundation.Crypto.Semantics.Machine.NativeKeygen

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace ElGamal.PrimeOrderRepresentation

open Foundation.Probability
open scoped ENNReal

/-- The native key generator reads the existing parameter codec. It uses
one exactly uniform scalar for both its public key and its secret key. -/
theorem nativeKeygen_almostSureHalts (n : Nat) (x : Domain n) :
    Machine.AlmostSureHalts Machine.NativeKeygen.program (scalarRequest n x) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  exact Machine.NativeKeygen.almostSureHalts_from_frame n x.down.modulus
    x.down.generator.val.val x.down.scalarOrder x.down.modulus_prime.one_lt
    x.down.modulus_lt (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

private theorem encoded_keygen (n : Nat) (x : Domain n) [NeZero x.down.scalarOrder] :
    ((uniform (Fin x.down.scalarOrder)).map (fun a =>
      Machine.frame (Machine.Binary.encode (n+3) (x.down.generator.val.val^a.val % x.down.modulus)) ++
        Machine.frame (Machine.Binary.encode (n+3) a.val))) =
      ((embed n x).toElGamalInstance.scheme.keygen).map
        (fun keys : (embed n x).params.Element × (embed n x).params.Scalar =>
          Machine.frame ((elementCode n x).encode keys.1) ++
            Machine.frame ((scalarCode n x).encode keys.2)) := by
  have ideal : (embed n x).algebra.sampling.sampleScalar = uniform (Fin x.down.scalarOrder) := by
    change @uniform (Fin x.down.scalarOrder)
      (embed n x).algebra.sampling.scalarFintype
      (embed n x).algebra.sampling.scalarNonempty = _
    rw [show (embed n x).algebra.sampling.scalarFintype =
      inferInstanceAs (Fintype (Fin x.down.scalarOrder)) from Subsingleton.elim _ _]
    rfl
  change _ = ((embed n x).algebra.sampling.sampleScalar.map
    (fun a => ((embed n x).params.power (embed n x).params.generator a, a))).map
      (fun keys : (embed n x).params.Element × (embed n x).params.Scalar =>
        Machine.frame ((elementCode n x).encode keys.1) ++
          Machine.frame ((scalarCode n x).encode keys.2))
  let choices : PMF (embed n x).params.Scalar := uniform (Fin x.down.scalarOrder)
  have choicesEq : (embed n x).algebra.sampling.sampleScalar = choices := ideal
  rw [choicesEq, PMF.map_comp]
  have encoded : ((uniform (Fin x.down.scalarOrder)).map (fun a =>
      Machine.frame (Machine.Binary.encode (n+3) (x.down.generator.val.val^a.val % x.down.modulus)) ++
        Machine.frame (Machine.Binary.encode (n+3) a.val))) =
      choices.map (fun a =>
        Machine.frame ((elementCode n x).encode ((embed n x).params.power (embed n x).params.generator a)) ++
          Machine.frame ((scalarCode n x).encode a)) := by
    apply congrArg (fun f : Fin x.down.scalarOrder → List Bool => (uniform (Fin x.down.scalarOrder)).map f)
    funext a
    change _ = Machine.frame (x.down.elementCode.encode
      (x.down.parameters.power x.down.parameters.generator a)) ++
        Machine.frame (x.down.scalarCode.encode a)
    have power := x.down.elementCode_power x.down.parameters.generator a
    rw [power]
    rfl
  exact encoded

/-- Actual finite code, including the full rejection distribution, realizes
the existing ElGamal key-generation law with the existing element/scalar codecs. -/
theorem nativeKeygen_exact (n : Nat) (x : Domain n) :
    Machine.evalLimit Machine.NativeKeygen.program (scalarRequest n x)
      (nativeKeygen_almostSureHalts n x) =
      ((embed n x).toElGamalInstance.scheme.keygen).map (fun keys : (embed n x).params.Element × (embed n x).params.Scalar =>
        Machine.frame ((elementCode n x).encode keys.1) ++
          Machine.frame ((scalarCode n x).encode keys.2)) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  let : NeZero x.down.scalarOrder := ⟨x.down.scalarOrder_prime.ne_zero⟩
  have law := Machine.NativeKeygen.evalLimit_from_frame n x.down.modulus
    x.down.generator.val.val x.down.scalarOrder x.down.modulus_prime.one_lt
    x.down.modulus_lt (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)
  exact law.trans (encoded_keygen n x)

noncomputable def keygenExpectedBudget (n : Nat) (x : Domain n) : Nat :=
  Machine.SavedFramedScalarInput.validBudget n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) + 1 +
      Machine.NativeKeygenSample.expectedBudget n

theorem nativeKeygen_expectedSteps (n : Nat) (x : Domain n) :
    Machine.expectedSteps Machine.NativeKeygen.program (scalarRequest n x) ≤
      (keygenExpectedBudget n x : ℝ≥0∞) := by
  let : NeZero x.down.modulus := ⟨x.down.modulus_prime.ne_zero⟩
  exact Machine.NativeKeygen.expectedSteps_from_frame n x.down.modulus
    x.down.generator.val.val x.down.scalarOrder x.down.modulus_prime.one_lt
    x.down.modulus_lt (ZMod.val_lt _) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

theorem keygenExpectedBudget_polynomiallyBounded (F : (n : Nat) → Domain n) :
    PolynomiallyBounded (fun n => keygenExpectedBudget n (F n)) :=
  Machine.NativeKeygen.expectedBudget_polynomiallyBounded
    (fun n => (F n).down.modulus) (fun n => (F n).down.generator.val.val)

end ElGamal.PrimeOrderRepresentation
