import Foundation.Constructions.ElGamal.PrimeOrderGroup
import Foundation.Constructions.ElGamal.MachineRepresented
import Foundation.Crypto.Semantics.Machine.RejectionSamplingSemantics

namespace ElGamal.PrimeOrderRepresentation

open Foundation.Probability

/-- The represented interface's universe is respected without altering the
underlying prime-order parameter structure or any core goal universe. -/
abbrev Domain (n : Nat) := ULift.{1} (PrimeOrderParameters n)

private theorem sampling_unique {params : DDHParameters}
    (first second : DDHFiniteSampling params) : first = second := by
  cases first
  cases second
  congr 1
  exact Subsingleton.elim _ _

/-- The ideal experiment selects the unique finite, nonempty scalar sampling
data whenever they exist. This is a mathematical specification, not machine
code for deciding finiteness, generating parameters, or sampling a scalar. -/
noncomputable def sampling (_ : Nat) (params : DDHParameters) :
    Option (DDHFiniteSampling params) := by
  classical
  exact if h : Nonempty (DDHFiniteSampling params) then some (Classical.choice h) else none

private theorem sampling_eq (n : Nat) (params : DDHParameters)
    (witness : DDHFiniteSampling params) : sampling n params = some witness := by
  classical
  have h : Nonempty (DDHFiniteSampling params) := ⟨witness⟩
  simp only [sampling, dif_pos h]
  exact congrArg some (sampling_unique _ witness)

/-- The concrete instance uses the previously proved group decryptor. No
arbitrary decryption function or unproved algebra law is a parameter. -/
noncomputable def embed (n : Nat) (x : Domain n) : ConcreteInstance sampling n where
  params := x.down.parameters
  algebra := x.down.finiteAlgebra
  decrypt := groupDecrypt x.down.parameters
  sampling_eq := sampling_eq n _ _

theorem embed_correct (n : Nat) (x : Domain n) :
    (embed n x).toElGamalInstance.scheme.Correct :=
  x.down.scheme_correct

/-- Universe lifting changes neither the serialized parameter fields nor
their lengths. Decoding still uses the mathematical validity specification. -/
noncomputable def instanceCode (n : Nat) : Machine.FiniteBitEncoding (Domain n) where
  encode x := (PrimeOrderParameters.instanceCode n).encode x.down
  decode bits := ((PrimeOrderParameters.instanceCode n).decode bits).map ULift.up
  decode_encode := by
    intro x
    rw [(PrimeOrderParameters.instanceCode n).decode_encode]
    rfl

@[simp] theorem instanceCode_length (n : Nat) (x : Domain n) :
    ((instanceCode n).encode x).length = 3 * (n + 3) :=
  PrimeOrderParameters.instanceCode_length n x.down

noncomputable def elementCode (n : Nat) (x : Domain n) :
    Machine.FiniteBitEncoding (embed n x).params.Element := x.down.elementCode

@[simp] theorem elementCode_length (n : Nat) (x : Domain n)
    (a : (embed n x).params.Element) : ((elementCode n x).encode a).length = n + 3 :=
  x.down.elementCode_length a

def scalarCode (n : Nat) (x : Domain n) :
    Machine.FiniteBitEncoding (embed n x).params.Scalar := x.down.scalarCode

@[simp] theorem scalarCode_length (n : Nat) (x : Domain n)
    (a : (embed n x).params.Scalar) : ((scalarCode n x).encode a).length = n + 3 :=
  x.down.scalarCode_length a

private theorem idealScalar_uniform (n : Nat) (x : Domain n)
    [NeZero x.down.scalarOrder] :
    (embed n x).algebra.sampling.sampleScalar = uniform (Fin x.down.scalarOrder) := by
  change @uniform (Fin x.down.scalarOrder)
    (embed n x).algebra.sampling.scalarFintype
    (embed n x).algebra.sampling.scalarNonempty = _
  have hFintype : (embed n x).algebra.sampling.scalarFintype =
      inferInstanceAs (Fintype (Fin x.down.scalarOrder)) := Subsingleton.elim _ _
  rw [hFintype]
  rfl

/-- The single rejection-sampling code realizes this concrete instance's
ideal scalar PMF, after the mathematical decoder for the raw binary modulus
width is applied. The theorem charges the actual expected execution and does
not install that decoder as a machine instruction. Framing and padding to the
instance's larger fixed-width scalar code remain separate code obligations. -/
theorem scalarSampler_exact (n : Nat) (x : Domain n) :
    let q := x.down.scalarOrder
    let code := Machine.Binary.fin q q.bits.length
      (by simpa using (Machine.Binary.value_lt q.bits).le)
    (Machine.evalLimit Machine.RejectionSampling.program q.bits
      (Machine.RejectionSampling.expectedPolynomialTime.almostSureHalts q.bits)).map code.decode =
        ((embed n x).algebra.sampling.sampleScalar).map some := by
  let : NeZero x.down.scalarOrder := ⟨x.down.scalarOrder_prime.ne_zero⟩
  dsimp only
  rw [idealScalar_uniform]
  exact Machine.RejectionSampling.evalLimit_nat_decoded x.down.scalarOrder

end ElGamal.PrimeOrderRepresentation
