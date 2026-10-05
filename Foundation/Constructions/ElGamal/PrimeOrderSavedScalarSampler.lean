import Foundation.Constructions.ElGamal.PrimeOrderScalarSampler
import Foundation.Machine.SavedFramedScalarSamplerSemantics

namespace ElGamal.PrimeOrderRepresentation

open scoped ENNReal

/-- The sampler used before native key generation retains the public
request on its actual input tape. Its observable scalar law is still exact. -/
theorem savedFramedScalarSampler_almostSureHalts (n : Nat) (x : Domain n) :
    Machine.AlmostSureHalts Machine.SavedFramedScalarSampler.program (scalarRequest n x) := by
  exact Machine.SavedFramedScalarSampler.almostSureHalts_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

theorem savedFramedScalarSampler_exact (n : Nat) (x : Domain n) :
    Machine.evalLimit Machine.SavedFramedScalarSampler.program (scalarRequest n x)
      (savedFramedScalarSampler_almostSureHalts n x) =
      ((embed n x).algebra.sampling.sampleScalar).map ((scalarCode n x).encode) := by
  let : NeZero x.down.scalarOrder := ⟨x.down.scalarOrder_prime.ne_zero⟩
  have law := Machine.SavedFramedScalarSampler.evalLimit_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)
  have ideal := (framedScalarSampler_exact n x).symm
  have standalone := Machine.FramedScalarSampler.evalLimit_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)
  exact law.trans (standalone.symm.trans ideal.symm)

noncomputable def savedScalarExpectedBudget (n : Nat) (x : Domain n) : Nat :=
  Machine.SavedFramedScalarInput.validBudget n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) + 1 + 50*(n+4)

theorem savedFramedScalarSampler_expectedSteps (n : Nat) (x : Domain n) :
    Machine.expectedSteps Machine.SavedFramedScalarSampler.program (scalarRequest n x) ≤
      (savedScalarExpectedBudget n x : ℝ≥0∞) := by
  exact Machine.SavedFramedScalarSampler.expectedSteps_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

theorem savedScalarExpectedBudget_polynomiallyBounded (F : (n : Nat) → Domain n) :
    PolynomiallyBounded (fun n => savedScalarExpectedBudget n (F n)) :=
  Machine.SavedFramedScalarSampler.expectedBudget_fixedWidth_polynomiallyBounded
    (fun n => (F n).down.modulus) (fun n => (F n).down.generator.val.val)

end ElGamal.PrimeOrderRepresentation
