import Foundation.Crypto.Semantics.Oracle.StatefulDiagramCanonical
import Foundation.Examples.StatefulDiagramNormalizationBoundary

/-! Canonical words and executable certificates for partial independence,
including the former nonconfluent peak and repeated operation identifiers. -/
namespace Foundation.Examples.StatefulDiagramCanonical
open CryptoOracle.StatefulDiagram
open Foundation.Examples.StatefulDiagramNormalizationBoundary (signature)

theorem peak_canonical : canonicalWord signature [2, 1, 0] = [1, 2, 0] := by decide_cbv

theorem both_terminals_canonical : canonicalWord signature [1, 2, 0] = canonicalWord signature [2, 0, 1] := by
  decide_cbv

theorem dependent_order_distinguished : canonicalWord signature [2, 0] ≠ canonicalWord signature [0, 2] := by
  decide_cbv

theorem multiplicity_preserved : canonicalWord signature [1, 2, 1, 0] = [1, 1, 2, 0] := by decide_cbv

def peakCertificate : Exchange signature [2, 1, 0] (canonicalWord signature [2, 1, 0]) :=
  canonicalCertificate signature [2, 1, 0]

def terminalCertificate : Exchange signature [2, 0, 1] (canonicalWord signature [2, 0, 1]) :=
  canonicalCertificate signature [2, 0, 1]

theorem peakCertificate_count : peakCertificate.swapCount signature = 1 := by rfl

theorem terminalCertificate_count : terminalCertificate.swapCount signature = 2 := by rfl

/-- State updates are forbidden by this signature, but private total PMF
sampling remains permitted and unobserved, as in the earlier self-loop case. -/
def readOnly (_ : Unit) : Interface Unit := ⟨∅, ∅⟩

theorem readOnly_repetition : canonicalWord readOnly [(), (), ()] = [(), (), ()] := by decide_cbv

theorem readOnly_certificate_count :
    (canonicalCertificate readOnly [(), (), ()]).swapCount readOnly = 0 := by rfl

/-- info: ([1, 2, 0], [1, 2, 0], [1, 1, 2, 0], 1, 2, 0) -/
#guard_msgs in
#eval (canonicalWord signature [2, 1, 0], canonicalWord signature [2, 0, 1],
  canonicalWord signature [1, 2, 1, 0], peakCertificate.swapCount signature,
  terminalCertificate.swapCount signature, (canonicalCertificate readOnly [(), (), ()]).swapCount readOnly)

end Foundation.Examples.StatefulDiagramCanonical
