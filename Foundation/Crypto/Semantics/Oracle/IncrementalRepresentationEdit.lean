import Foundation.Logic.FiniteCodecRepair
import Foundation.Crypto.Semantics.Oracle.ScopedRepresentationEdit

/-! Reuse an accepted declaration to generate a new representation edit by
checking only the changed intersection. The result is exactly the existing
full scoped generator, so the same operational joint guarantee applies. -/
namespace CryptoOracle.RandomOracle.Representation.IncrementalEdit
open Foundation.Probability Foundation.Logic
variable {width : Nat} {Input Label OldStored NewStored Result : Type}
  [DecidableEq Input] [DecidableEq Label] [Fintype Label]

noncomputable def generate
    (changed : Finset (Label × Input))
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true)
    (unchanged : ∀ index ∈ ScopedEdit.used program saved, index ∉ changed → left index = right index) :=
  (FiniteCodecRepair.compile (ScopedEdit.used program saved) changed left right accepted unchanged).map fun family =>
    (family, Switch.joint old (GeneratedEdit.codecs family pack) choose count program saved)

theorem generate_eq_full
    (changed : Finset (Label × Input))
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true)
    (unchanged : ∀ index ∈ ScopedEdit.used program saved, index ∉ changed → left index = right index) :
    generate changed left right old pack choose count program saved accepted unchanged =
      ScopedEdit.generate right old pack choose count program saved := by
  simp only [generate, ScopedEdit.generate, FiniteCodecRepair.compile_eq_full]

theorem generate_sound
    (changed : Finset (Label × Input))
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (accepted : (FiniteCodecRestriction.compile (ScopedEdit.used program saved) left).isSome = true)
    (unchanged : ∀ index ∈ ScopedEdit.used program saved, index ∉ changed → left index = right index)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate changed left right old pack choose count program saved accepted unchanged = some (family, law)) :
    law = GeneratedEdit.rawJoint right old pack choose count program saved ∧
      law.map (Switch.decode old (GeneratedEdit.codecs family pack)) = Switch.reference old choose count program saved := by
  rw [generate_eq_full] at generated
  exact ScopedEdit.generate_sound right old pack choose count program saved family law generated

end CryptoOracle.RandomOracle.Representation.IncrementalEdit
