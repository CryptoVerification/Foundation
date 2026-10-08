import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! Faithful bit input for an observer of native code, full state and time.
The unary time field has explicit length. This bounds the supplied input;
it does not assert a unit-cost serializer or loader implementation. -/
namespace Machine.TimedConfigurationEncoding
open Foundation.Probability TimedExecution

def encoding : FiniteBitEncoding ((Program × Configuration) × Nat) :=
  StructuredCodeEncoding.completeEncoding.prod ConfigurationEncoding.unary

def encode (code : Program) (result : Configuration × Nat) : List Bool :=
  encoding.encode ((code, result.1), result.2)

/-- The fixed code is retained in the bits while the represented value is a state/time pair. -/
def resultEncoding (code : Program) : FiniteBitEncoding (Configuration × Nat) :=
  encoding.retract (fun result => ((code, result.1), result.2))
    (fun fields => (fields.1.2, fields.2)) (fun _ => rfl)

theorem resultEncoding_encode (code : Program) (result : Configuration × Nat) :
    (resultEncoding code).encode result = encode code result := rfl

theorem decode_encode (code : Program) (result : Configuration × Nat) :
    encoding.decode (encode code result) = some ((code, result.1), result.2) := encoding.decode_encode _

theorem encode_length (code : Program) (result : Configuration × Nat) :
    (encode code result).length =
      2 * (StructuredCodeEncoding.completeEncoding.encode (code, result.1)).length + 1 + result.2 := by
  simp [encode, encoding, FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.unary]

def bound (code : Program) (pc cells fuel : Nat) : Nat :=
  2 * StructuredCodeEncoding.bound code pc cells fuel + 1 + fuel

/-- Every supported first-boundary outcome has a polynomial-size faithful input. -/
theorem boundary_length (code : Program) (boundary : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support) :
    (encode code result).length ≤ bound code start.pc start.tapeCells fuel := by
  have hTime := runToBoundary_bounded (stepPMF code) boundary fuel start result hResult
  have hSpace := StructuredCodeEncoding.boundary code boundary fuel start result hResult
  have hMono := StructuredCodeEncoding.bound_mono code (Nat.le_refl start.pc) (Nat.le_refl start.tapeCells) hTime
  rw [encode_length]
  unfold bound
  omega

theorem bound_polynomial (code : Program) {pc cells fuel : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells) (hFuel : PolynomiallyBounded fuel) :
    PolynomiallyBounded (fun n => bound code (pc n) (cells n) (fuel n)) :=
  (((PolynomiallyBounded.const 2).mul
    (StructuredCodeEncoding.bound_polynomial code hPc hCells hFuel)).add
      (PolynomiallyBounded.const 1)).add hFuel

end Machine.TimedConfigurationEncoding
