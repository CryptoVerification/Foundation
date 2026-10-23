import Foundation.Logic.FiniteCodecDifference
import Foundation.Crypto.Semantics.Oracle.ScopedRepresentationEdit

/-! Generate a new representation edit from two forward declarations and an
old acceptance certificate. The exact changed rows and the unchanged-row proof
are computed internally. No user-supplied difference or inverse is required. -/
namespace CryptoOracle.RandomOracle.Representation.AutomaticEdit
open Foundation.Probability Foundation.Logic
variable {width : Nat} {Input Label OldStored NewStored Result : Type}
  [DecidableEq Input] [DecidableEq Label] [Fintype Label]

noncomputable def generate
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true) :=
  (FiniteCodecDifference.compile (ScopedEdit.used program saved) left right accepted).map fun family =>
    (family, Switch.joint old (GeneratedEdit.codecs family pack) choose count program saved)

theorem generate_eq_full
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true) :
    generate left right old pack choose count program saved accepted =
      ScopedEdit.generate right old pack choose count program saved := by
  simp only [generate, ScopedEdit.generate, FiniteCodecDifference.compile_eq_full]

theorem generate_sound
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate left right old pack choose count program saved accepted = some (family, law)) :
    law = GeneratedEdit.rawJoint right old pack choose count program saved ∧
      law.map (Switch.decode old (GeneratedEdit.codecs family pack)) = Switch.reference old choose count program saved := by
  rw [generate_eq_full] at generated
  exact ScopedEdit.generate_sound right old pack choose count program saved family law generated

end CryptoOracle.RandomOracle.Representation.AutomaticEdit
