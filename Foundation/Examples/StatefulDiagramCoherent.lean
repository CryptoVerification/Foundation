import Foundation.Crypto.Semantics.Oracle.StatefulDiagramCoherent
import Foundation.Examples.StatefulDiagramAnalysisTransport
import Foundation.Examples.StatefulDiagramHorizontal

/-! Run the general coherence constructor without supplying a comparison
cell: braids, separated edits, composite inverses, repeated-ID loops and the
empty word all use the same source-length recursion. -/
namespace Foundation.Examples.StatefulDiagramCoherent
open CryptoOracle.StatefulDiagram
open Foundation.Examples.StatefulDiagramAnalysisTransport

/-- The earlier hand-written braid comparison is not supplied as input. -/
def automaticBraid : HorizontalCoherence Checked.signature Checked.left Checked.right :=
  exchangeCoherent Checked.signature Checked.left Checked.right

def automaticSeparated : HorizontalCoherence StatefulDiagramHorizontal.signature
    StatefulDiagramHorizontal.leftFirst StatefulDiagramHorizontal.rightFirst :=
  exchangeCoherent StatefulDiagramHorizontal.signature
    StatefulDiagramHorizontal.leftFirst StatefulDiagramHorizontal.rightFirst

def automaticComposite : HorizontalCoherence StatefulDiagramHorizontal.signature
    (horizontalLeft StatefulDiagramHorizontal.signature StatefulDiagramHorizontal.leftWithBacktrack
      StatefulDiagramHorizontal.rightWithInverses)
    (horizontalRight StatefulDiagramHorizontal.signature StatefulDiagramHorizontal.leftWithBacktrack
      StatefulDiagramHorizontal.rightWithInverses) :=
  exchangeCoherent StatefulDiagramHorizontal.signature _ _

/-- The former parity obstruction is handled by the same general algorithm. -/
def automaticSelf : HorizontalCoherence HigherBoundary.readOnly HigherBoundary.selfSwap HigherBoundary.identityPath :=
  exchangeCoherent HigherBoundary.readOnly HigherBoundary.selfSwap HigherBoundary.identityPath

def emptyPath : Exchange Checked.signature [] [] :=
  ((Exchange.refl []).symm.trans (.refl [])).symm

def automaticEmpty : HorizontalCoherence Checked.signature emptyPath (.refl []) :=
  exchangeCoherent Checked.signature emptyPath (.refl [])

theorem old_obstruction_connected : Nonempty (HorizontalCoherence HigherBoundary.readOnly
    HigherBoundary.selfSwap HigherBoundary.identityPath) := ⟨automaticSelf⟩

def automaticCanonicalFactor := canonicalFactor Checked.signature Checked.left

/-- info: (0, 1, 1, 0, 0, 0) -/
#guard_msgs in
#eval (automaticBraid.squareCount Checked.signature,
  automaticSeparated.squareCount StatefulDiagramHorizontal.signature,
  automaticComposite.squareCount StatefulDiagramHorizontal.signature,
  automaticSelf.squareCount HigherBoundary.readOnly, automaticEmpty.squareCount Checked.signature,
  automaticCanonicalFactor.squareCount Checked.signature)

end Foundation.Examples.StatefulDiagramCoherent
