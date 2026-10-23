import Foundation.Logic.FiniteCodecRestriction
import Foundation.Crypto.Semantics.Oracle.GeneratedRepresentationEdit
import Foundation.Crypto.Semantics.Oracle.RepresentationScope

/-! Generate representation edits from the extracted query footprint PLUS
initial cache keys. Input need not be finite. Unchecked entries are completed
by identity only inside the proof artifact; the theorem compares against the
actual raw declaration on every supported execution, retaining the prefix. -/
namespace CryptoOracle.RandomOracle.Representation.ScopedEdit
open Foundation.Probability Foundation.Logic
variable {width : Nat} {Input Label OldStored NewStored Result : Type}
  [DecidableEq Input] [DecidableEq Label] [Fintype Label]

def used (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) : Finset (Label × Input) :=
  Finset.univ.product (Scope.allowed program saved)

omit [DecidableEq Label] in
theorem used_pair (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (label : Label) (input : Input) :
    (label, input) ∈ used program saved ↔ input ∈ Scope.allowed program saved := by
  simp [used]

theorem oracle_on (allowed : Finset Input)
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (compiled : FiniteCodecRestriction.compile (Finset.univ.product allowed) encoder = some family)
    (pack : Fin (width + 1) ≃ NewStored) (label : Label) (input : Input) (included : input ∈ allowed)
    (saved : Table Input NewStored) :
    oracle (GeneratedEdit.codecs family pack label) saved input =
      GeneratedEdit.rawOracle (fun input => encoder (label, input)) pack saved input := by
  have member : (label, input) ∈ Finset.univ.product allowed := by simp [included]
  simp only [oracle, GeneratedEdit.rawOracle, GeneratedEdit.codecs, Equiv.trans_apply, Equiv.symm_trans_apply,
    FiniteCodecRestriction.forward_spec _ encoder family compiled (label, input) member,
    FiniteCodecRestriction.inverse_spec _ encoder family compiled (label, input) member]
  rfl

theorem run_on (allowed : Finset Input)
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (compiled : FiniteCodecRestriction.compile (Finset.univ.product allowed) encoder = some family)
    (pack : Fin (width + 1) ≃ NewStored) (label : Label)
    (program : Program Input (Fin (width + 1)) Result) (within : program.footprint ⊆ allowed)
    (saved : Table Input NewStored) :
    program.run (oracle (GeneratedEdit.codecs family pack label)) saved =
      program.run (GeneratedEdit.rawOracle (fun input => encoder (label, input)) pack) saved := by
  apply Program.run_congr_on_footprint
  intro input member state
  exact oracle_on allowed encoder family compiled pack label input (within member) state

theorem recode_on (allowed : Finset Input)
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (compiled : FiniteCodecRestriction.compile (Finset.univ.product allowed) encoder = some family)
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (label : Label) (saved : Table Input OldStored) (within : Scope.keysWithin allowed saved) :
    Switch.recode old (GeneratedEdit.codecs family pack label) saved =
      GeneratedEdit.rawRecode (fun input => encoder (label, input)) old pack saved := by
  simp only [Switch.recode, table, GeneratedEdit.rawRecode, GeneratedEdit.codecs, Equiv.trans_apply]
  apply List.map_congr_left
  intro entry member
  have included : (label, entry.1) ∈ Finset.univ.product allowed := by simp [within entry member]
  rw [FiniteCodecRestriction.forward_spec _ encoder family compiled (label, entry.1) included]

theorem joint_matches_declaration
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (compiled : FiniteCodecRestriction.compile (used program saved) encoder = some family) :
    Switch.joint old (GeneratedEdit.codecs family pack) choose count program saved =
      GeneratedEdit.rawJoint encoder old pack choose count program saved := by
  simp only [Switch.joint, GeneratedEdit.rawJoint]
  apply bind_congr_of_support
  intro past supported
  obtain ⟨keys, remaining⟩ := Scope.prefix_scope old program count saved past supported
  rw [recode_on (Scope.allowed program saved) encoder family compiled old pack (choose past) past.state keys]
  rw [run_on (Scope.allowed program saved) encoder family compiled pack (choose past) past.result remaining]

noncomputable def generate
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) :
    Option ((Label × Input → Fin (width + 1) ≃ Fin (width + 1)) ×
      PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored)) :=
  (FiniteCodecRestriction.compile (used program saved) encoder).map fun family =>
    (family, Switch.joint old (GeneratedEdit.codecs family pack) choose count program saved)

/-- If declarations agree on the extracted scope, no generated codec or
retained game changes. This is an equality of artifacts, not a runtime bound. -/
theorem generate_congr
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (agree : ∀ label input, input ∈ Scope.allowed program saved → left (label, input) = right (label, input)) :
    generate left old pack choose count program saved = generate right old pack choose count program saved := by
  unfold generate
  rw [FiniteCodecRestriction.compile_congr (used program saved) left right
    (fun index member => agree index.1 index.2 ((used_pair program saved index.1 index.2).mp member))]

/-- Outside-scope declaration edits preserve the full raw operational joint law
whenever the common checked scope compiles successfully. -/
theorem raw_joint_congr
    (left right : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (compiled : FiniteCodecRestriction.compile (used program saved) left = some family)
    (agree : ∀ label input, input ∈ Scope.allowed program saved → left (label, input) = right (label, input)) :
    GeneratedEdit.rawJoint left old pack choose count program saved =
      GeneratedEdit.rawJoint right old pack choose count program saved := by
  have same := FiniteCodecRestriction.compile_congr (used program saved) left right
    (fun index member => agree index.1 index.2 ((used_pair program saved index.1 index.2).mp member))
  have rightCompiled : FiniteCodecRestriction.compile (used program saved) right = some family := same.symm.trans compiled
  exact (joint_matches_declaration left family old pack choose count program saved compiled).symm.trans
    (joint_matches_declaration right family old pack choose count program saved rightCompiled)

theorem generate_complete
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) :
    (generate encoder old pack choose count program saved).isSome = true ↔
      ∀ label input, input ∈ Scope.allowed program saved → Function.Bijective (encoder (label, input)) := by
  simp only [generate, Option.isSome_map]
  rw [FiniteCodecRestriction.complete]
  constructor
  · intro checked label input included
    exact checked (label, input) ((used_pair program saved label input).mpr included)
  · intro checked index included
    exact checked index.1 index.2 ((used_pair program saved index.1 index.2).mp included)

theorem generate_sound
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate encoder old pack choose count program saved = some (family, law)) :
    law = GeneratedEdit.rawJoint encoder old pack choose count program saved ∧
      law.map (Switch.decode old (GeneratedEdit.codecs family pack)) = Switch.reference old choose count program saved := by
  rw [generate, Option.map_eq_some_iff] at generated
  obtain ⟨compiled, accepted, same⟩ := generated
  cases same
  exact ⟨joint_matches_declaration encoder family old pack choose count program saved accepted,
    Switch.decoded_joint old (GeneratedEdit.codecs family pack) choose count program saved⟩

theorem generated_final
    (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate encoder old pack choose count program saved = some (family, law)) :
    law.map (fun pair => (Switch.decode old (GeneratedEdit.codecs family pack) pair).2.2) = program.run (oracle old) saved := by
  have joint := (generate_sound encoder old pack choose count program saved family law generated).2
  have projected := congrArg (fun p => p.map (fun pair => pair.2.2)) joint
  simpa only [PMF.map_comp, Function.comp_def, Switch.reference_final] using projected

end CryptoOracle.RandomOracle.Representation.ScopedEdit
