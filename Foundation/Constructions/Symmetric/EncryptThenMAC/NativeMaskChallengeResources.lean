import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskChallenge
import Foundation.Crypto.Semantics.Oracle.ResponseLoadingResources

/-! The incoming challenge's actual loading prefix, before the load-code halt.
These bounds cover all response bytes, the temporary tape, the saved machine,
external unit state, transcript and finite loading code. The complete outer
query/alignment/masking/observer controller is a separate composition task. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge.Resources
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def responseBound (width horizon : Nat) :=
  ResponseLoading.Resources.completeBound loadCode 0 (width + 3) 0 horizon

private theorem initial_cells {width : Nat} (key : Bits width) :
    SourceStorage.cells (fun _ : Unit => 0) (loadFrame key.toList) = width + 3 := by
  simp [SourceStorage.cells, SourceStorage.controlCells, SourceStorage.traceCells,
    loadFrame, Machine.Configuration.tapeCells, Tape.cells, Bits.length_toList]
  omega

/-- Every incoming response is covered, regardless of its distribution.
The analysis freezes at resume; no source instruction has yet executed. -/
theorem response_peak {width : Nat} (key : Bits width) (horizon elapsed : Nat)
    (hTime : elapsed ≤ horizon) (target : CryptoOracle.Interactive.Configuration Unit)
    (h : target ∈ (TimedExecution.eval
      (ResponseLoading.Resources.step loadCode NativeMaskReduction.oracle)
      elapsed (loadFrame key.toList)).support) :
    ((ResponseLoading.Resources.completeEncoding FiniteBitEncoding.unit).encode
      (loadCode, target)).length ≤ responseBound width horizon := by
  have hb := ResponseLoading.Resources.complete_peak FiniteBitEncoding.unit (fun _ : Unit => 0)
    (fun _ => Nat.le_refl 0) loadCode NativeMaskReduction.oracle horizon elapsed hTime
    (loadFrame key.toList) target trivial h
  rw [initial_cells] at hb
  simpa only [responseBound, loadFrame, ConfigurationEncoding.pc,
    List.length_nil] using hb

/-- The original operational machine's first-arrival result is charged at
its actual cost, rather than the maximum response-loading budget. -/
theorem response_boundary {width : Nat} (key : Bits width) (fuel : Nat)
    (result : CryptoOracle.Interactive.Configuration Unit × Nat)
    (h : result ∈ (runToBoundary (Reification.timedStep loadCode NativeMaskReduction.oracle)
      (fun frame => ResponseLoading.Resources.boundary frame.control)
      fuel (loadFrame key.toList)).support) :
    ((ResponseLoading.Resources.completeEncoding FiniteBitEncoding.unit).encode
      (loadCode, result.1)).length ≤ responseBound width result.2 := by
  have hb := ResponseLoading.Resources.complete_boundary FiniteBitEncoding.unit (fun _ : Unit => 0)
    (fun _ => Nat.le_refl 0) loadCode NativeMaskReduction.oracle fuel
    (loadFrame key.toList) result trivial h
  rw [initial_cells] at hb
  simpa only [responseBound, loadFrame, ConfigurationEncoding.pc,
    List.length_nil] using hb

theorem response_complete {width : Nat} (key : Bits width)
    (result : CryptoOracle.Interactive.Configuration Unit × Nat)
    (h : result ∈ (runToBoundary (Reification.timedStep loadCode NativeMaskReduction.oracle)
      (fun frame => ResponseLoading.Resources.boundary frame.control)
      (3 * width + 2) (loadFrame key.toList)).support) :
    ResponseLoading.Resources.boundary result.1.control = true := by
  apply ResponseLoading.Resources.completes loadCode NativeMaskReduction.oracle {} () [] key.toList result
  simpa only [Bits.length_toList, loadFrame] using h

theorem responseBound_polynomial {width horizon : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => responseBound (width n) (horizon n)) :=
  ResponseLoading.Resources.completeBound_polynomial loadCode
    (PolynomiallyBounded.const 0) (hWidth.add (PolynomiallyBounded.const 3))
    (PolynomiallyBounded.const 0) hTime

end Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge.Resources
