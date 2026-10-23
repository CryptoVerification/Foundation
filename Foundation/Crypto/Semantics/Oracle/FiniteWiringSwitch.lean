import Foundation.Logic.Polygraph.StructuralWiringCompilation
import Foundation.Crypto.Semantics.Oracle.SharedReferenceSwitch

/-! Finite primitive wiring certificates lift to the same single captured
live-cache execution. The certificate is in the complete strict wiring
calculus, not the previous incomplete nine-root source Cell language. -/
namespace CryptoOracle.RandomOracle.Representation.SharedSwitch
open Foundation.Probability Foundation.Logic.Polygraph
open StructuralTransport
variable {Input Response Result OldStored NewStored Label : Type}
  [DecidableEq Input] [Fintype Response] [Nonempty Response]
  {first last : Shape Unit}

theorem compiled_cell_joint {one two : Wire first last}
    (cell : FiniteWiring.Cell (Finite.compile one) (Finite.compile two))
    (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (inputs : Switch.Past Input Response Result OldStored → first.Value (fun _ => SharedReference.Ref))
    (route : Switch.Past Input Response Result OldStored → last.Value (fun _ => SharedReference.Ref) → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    wired old codecs choose one inputs route count program saved = wired old codecs choose two inputs route count program saved := by
  unfold wired
  have same : (fun past => one.eval (fun _ => SharedReference.Ref) (inputs past)) =
      (fun past => two.eval (fun _ => SharedReference.Ref) (inputs past)) :=
    funext (fun past => Finite.compiled_cell_sound cell (inputs past))
  rw [same]

end CryptoOracle.RandomOracle.Representation.SharedSwitch
