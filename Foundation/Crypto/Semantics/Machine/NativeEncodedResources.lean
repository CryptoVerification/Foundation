import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! A decodable bit representation of native code and complete configuration,
with bounds for every prefix and every actual first-arrival boundary outcome.
Framing is counted explicitly. No halt or cryptographic premise is needed.
This measures represented storage, not the cost of computing the encoding. -/
namespace Machine
open Foundation.Probability TimedExecution

abbrev Program.bitEncoding : FiniteBitEncoding Program :=
  ⟨Program.encode, Program.decode, Program.decode_encode⟩

namespace NativeEncodedResources

def completeEncoding : FiniteBitEncoding (Program × Configuration) :=
  Program.bitEncoding.prod ConfigurationEncoding.configuration

theorem complete_length (code : Program) (machine : Configuration) :
    (completeEncoding.encode (code, machine)).length =
      2 * (Program.encode code).length + 1 + (ConfigurationEncoding.configuration.encode machine).length := by
  rw [completeEncoding, FiniteBitEncoding.prod_encode_length]

def bound (code : Program) (initialPc initialCells horizon : Nat) : Nat :=
  code.storageBound initialPc initialCells horizon + (Program.encode code).length + 1

theorem bound_mono (code : Program) {pc nextPc cells nextCells time nextTime : Nat}
    (hPc : pc ≤ nextPc) (hCells : cells ≤ nextCells) (hTime : time ≤ nextTime) :
    bound code pc cells time ≤ bound code nextPc nextCells nextTime := by
  have hm := Nat.mul_le_mul_right (code.addressCap + 1) hTime
  unfold bound Program.storageBound
  omega

/-- Counts the actual finite code once, both tape zippers, head positions,
program counter, halt flag and all delimiters, on every supported prefix. -/
theorem peak (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF code) elapsed start).support) :
    (completeEncoding.encode (code, target)).length ≤ bound code start.pc start.tapeCells horizon := by
  have hb := codeAndStateBits_prefix code horizon elapsed hElapsed start target h
  rw [complete_length]
  unfold bound Configuration.codeAndStateBits at *
  omega

/-- Actual stopping time and storage stay correlated. The boundary may be
an active subroutine return rather than the final halt. -/
theorem boundary (code : Program) (stop : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (h : result ∈ (runToBoundary (stepPMF code) stop fuel start).support) :
    (completeEncoding.encode (code, result.1)).length ≤ bound code start.pc start.tapeCells result.2 := by
  have hp := ResourceGrowth.boundary_endpoint (stepPMF code) Configuration.pc
    (code.addressCap + 1) (pc_le_of_support code) stop fuel start result h
  have ht := tapeCells_boundary code stop fuel start result h
  have he := ConfigurationEncoding.configuration_length_le result.1
  rw [complete_length]
  unfold bound Program.storageBound
  omega

theorem bound_polynomial (code : Program) {pc cells time : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells)
    (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (fun n => bound code (pc n) (cells n) (time n)) :=
  ((storageBound_polynomial code hPc hCells hTime).add
    (PolynomiallyBounded.const (Program.encode code).length)).add (PolynomiallyBounded.const 1)

/-- Every native procedure inherits the faithful whole-prefix certificate. -/
theorem procedure_peak {Input Output : Type*} (P : Machine.Procedure Input Output)
    (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ P.execution.budget input)
    (target : Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF P.code) elapsed (P.execution.entry input)).support) :
    (completeEncoding.encode (P.code, target)).length ≤
      bound P.code (P.execution.entry input).pc (P.execution.entry input).tapeCells (P.execution.budget input) :=
  peak P.code _ elapsed hElapsed _ target h

end NativeEncodedResources
end Machine
