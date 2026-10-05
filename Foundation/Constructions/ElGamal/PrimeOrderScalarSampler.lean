import Foundation.Constructions.ElGamal.PrimeOrderRepresentation
import Foundation.Machine.FramedScalarSamplerSemantics

namespace ElGamal.PrimeOrderRepresentation

open Foundation.Probability
open scoped ENNReal

/-- The actual public request read by the finite framed scalar program. -/
noncomputable def scalarRequest (n : Nat) (x : Domain n) : List Bool :=
  Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x)

theorem framedScalarSampler_almostSureHalts (n : Nat) (x : Domain n) :
    Machine.AlmostSureHalts Machine.FramedScalarSampler.program (scalarRequest n x) := by
  exact Machine.FramedScalarSampler.almostSureHalts_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

/-- The finite framed machine emits the existing scalar codec with exactly
the construction's ideal scalar distribution. This includes physical frame
reading, modulus canonicalization, retries, fixed-width padding and halt. -/
theorem framedScalarSampler_exact (n : Nat) (x : Domain n) :
    Machine.evalLimit Machine.FramedScalarSampler.program (scalarRequest n x)
      (framedScalarSampler_almostSureHalts n x) =
      ((embed n x).algebra.sampling.sampleScalar).map ((scalarCode n x).encode) := by
  let : NeZero x.down.scalarOrder := ⟨x.down.scalarOrder_prime.ne_zero⟩
  have law := Machine.FramedScalarSampler.evalLimit_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)
  have ideal : (embed n x).algebra.sampling.sampleScalar = uniform (Fin x.down.scalarOrder) := by
    change @uniform (Fin x.down.scalarOrder)
      (embed n x).algebra.sampling.scalarFintype
      (embed n x).algebra.sampling.scalarNonempty = _
    have finiteType : (embed n x).algebra.sampling.scalarFintype =
        inferInstanceAs (Fintype (Fin x.down.scalarOrder)) := Subsingleton.elim _ _
    rw [finiteType]
    rfl
  rw [ideal]
  exact law

noncomputable def scalarExpectedBudget (n : Nat) (x : Domain n) : Nat :=
  Machine.FramedScalarInput.validBudget n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) + 1 + 50*(n+4)

theorem framedScalarSampler_expectedSteps (n : Nat) (x : Domain n) :
    Machine.expectedSteps Machine.FramedScalarSampler.program (scalarRequest n x) ≤
      (scalarExpectedBudget n x : ℝ≥0∞) := by
  exact Machine.FramedScalarSampler.expectedSteps_from_frame n
    (Machine.Binary.encode (n+3) x.down.modulus)
    (Machine.Binary.encode (n+3) x.down.generator.val.val) x.down.scalarOrder
    (by simp) x.down.scalarOrder_prime.two_le
    (x.down.scalarOrder_lt_modulus.trans x.down.modulus_lt)

/-- Every valid parameter family has a polynomial expected-cost allowance.
This does not turn the unbounded rejection sampler into worst-case PPT. -/
theorem scalarExpectedBudget_polynomiallyBounded (F : (n : Nat) → Domain n) :
    PolynomiallyBounded (fun n => scalarExpectedBudget n (F n)) :=
  Machine.FramedScalarSampler.expectedBudget_fixedWidth_polynomiallyBounded
    (fun n => (F n).down.modulus) (fun n => (F n).down.generator.val.val)

end ElGamal.PrimeOrderRepresentation
