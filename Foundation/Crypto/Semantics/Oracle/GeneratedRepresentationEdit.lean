import Foundation.Logic.FiniteCodecGenerator
import Foundation.Crypto.Semantics.Oracle.RepresentationSwitch

/-! A checked frontend for finite representation declarations. It synthesizes
the inverse from the forward encoding, then generates the ACTUAL operational
switch game. Perfect randomized decoders cannot bypass a rejected collision
when their only input is the stored code. No synthesis of arbitrary program
relations, hidden auxiliary memory, or quantitative decoder bound is claimed. -/
namespace CryptoOracle.RandomOracle.Representation.GeneratedEdit
open Foundation.Probability Foundation.Logic
variable {width : Nat}

theorem randomized_decoder_iff (encoder : Fin (width + 1) → Fin (width + 1)) :
    (∃ decoder : Fin (width + 1) → PMF (Fin (width + 1)),
      ∀ value, decoder (encoder value) = PMF.pure value) ↔ FiniteCodecGenerator.validates encoder = true := by
  constructor
  · rintro ⟨decoder, correct⟩
    have injective : Function.Injective encoder := by
      intro left right same
      have equality : PMF.pure left = PMF.pure right :=
        (correct left).symm.trans ((congrArg decoder same).trans (correct right))
      have supported : left ∈ (PMF.pure left).support := by simp
      rw [equality] at supported
      simpa using supported
    exact (FiniteCodecGenerator.validates_iff encoder).mpr
      (FiniteCodecGenerator.inverse_of_injective encoder injective)
  · intro checked
    refine ⟨fun stored => PMF.pure (FiniteCodecGenerator.inverse encoder stored), ?_⟩
    intro value
    change PMF.pure (FiniteCodecGenerator.inverse encoder (encoder value)) = PMF.pure value
    rw [(FiniteCodecGenerator.validates_iff encoder).mp checked value]

variable {Input Label OldStored NewStored Result : Type}
  [DecidableEq Input] [Fintype Input] [Fintype Label]

def codecs (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (pack : Fin (width + 1) ≃ NewStored) (label : Label) (input : Input) : Fin (width + 1) ≃ NewStored :=
  (family (label, input)).trans pack

/-- Direct semantics of the forward declaration, defined even for rejected
colliding encodings. Its decoder uses the same first-preimage search. -/
noncomputable def rawOracle (encoder : Input → Fin (width + 1) → Fin (width + 1))
    (pack : Fin (width + 1) ≃ NewStored) : Oracle Input (Fin (width + 1)) (Table Input NewStored) :=
  fun saved input => match saved.lookup input with
    | some stored => PMF.pure (saved, FiniteCodecGenerator.inverse (encoder input) (pack.symm stored))
    | none => (uniform (Fin (width + 1))).map fun value => ((input, pack (encoder input value)) :: saved, value)

omit [Fintype Input] [Fintype Label] in
theorem raw_run_congr (left right : Input → Fin (width + 1) → Fin (width + 1))
    (pack : Fin (width + 1) ≃ NewStored) (allowed : Finset Input)
    (program : Program Input (Fin (width + 1)) Result) (within : program.footprint ⊆ allowed)
    (agree : ∀ input ∈ allowed, left input = right input) (saved : Table Input NewStored) :
    program.run (rawOracle left pack) saved = program.run (rawOracle right pack) saved := by
  apply Program.run_congr_on_footprint
  intro input member state
  simp only [rawOracle, agree input (within member)]

def rawRecode (encoder : Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (saved : Table Input OldStored) : Table Input NewStored :=
  saved.map fun entry => (entry.1, pack (encoder entry.1 ((old entry.1).symm entry.2)))

theorem compiled_oracle (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (compiled : FiniteCodecGenerator.compileFamily encoder = some family)
    (pack : Fin (width + 1) ≃ NewStored) (label : Label) :
    oracle (codecs family pack label) = rawOracle (fun input => encoder (label, input)) pack := by
  funext saved input
  simp only [oracle, rawOracle, codecs, Equiv.trans_apply, Equiv.symm_trans_apply,
    FiniteCodecGenerator.family_spec encoder family compiled,
    FiniteCodecGenerator.family_inverse_spec encoder family compiled]
  rfl

omit [DecidableEq Input] in
theorem compiled_recode (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (compiled : FiniteCodecGenerator.compileFamily encoder = some family)
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (label : Label) (saved : Table Input OldStored) :
    Switch.recode old (codecs family pack label) saved = rawRecode (fun input => encoder (label, input)) old pack saved := by
  simp only [Switch.recode, table, rawRecode, codecs, Equiv.trans_apply,
    FiniteCodecGenerator.family_spec encoder family compiled]

noncomputable def rawJoint (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) :=
  ((Program.pauseAfter count program).run (oracle old) saved).bind fun past =>
    (past.result.run (rawOracle (fun input => encoder (choose past, input)) pack)
      (rawRecode (fun input => encoder (choose past, input)) old pack past.state)).map fun last =>
        (past, choose past, {last with trace := past.trace ++ last.trace})

noncomputable def generate (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) :
    Option ((Label × Input → Fin (width + 1) ≃ Fin (width + 1)) ×
      PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored)) :=
  (FiniteCodecGenerator.compileFamily encoder).map fun family =>
    (family, Switch.joint old (codecs family pack) choose count program saved)

theorem generated_matches_edit (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate encoder old pack choose count program saved = some (family, law)) :
    law = rawJoint encoder old pack choose count program saved := by
  rw [generate, Option.map_eq_some_iff] at generated
  obtain ⟨compiled, accepted, same⟩ := generated
  cases same
  simp only [Switch.joint, rawJoint, compiled_oracle encoder family accepted,
    compiled_recode encoder family accepted]

theorem generate_complete (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored) :
    (generate encoder old pack choose count program saved).isSome = true ↔
      ∀ index, Function.Bijective (encoder index) := by
  simp only [generate, Option.isSome_map]
  exact FiniteCodecGenerator.family_complete encoder

/-- No inverse, equality of whole games, or proof diagram is an input to
generate. The resulting whole-joint theorem follows from checked declarations. -/
theorem generate_sound (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate encoder old pack choose count program saved = some (family, law)) :
    (∀ label input value, codecs family pack label input value = pack (encoder (label, input) value)) ∧
      law.map (Switch.decode old (codecs family pack)) = Switch.reference old choose count program saved := by
  rw [generate, Option.map_eq_some_iff] at generated
  obtain ⟨compiled, accepted, same⟩ := generated
  cases same
  refine ⟨?_, Switch.decoded_joint old (codecs family pack) choose count program saved⟩
  intro label input value
  simp only [codecs, Equiv.trans_apply,
    FiniteCodecGenerator.family_spec encoder family accepted (label, input) value]

theorem generated_final (encoder : Label × Input → Fin (width + 1) → Fin (width + 1))
    (old : Input → Fin (width + 1) ≃ OldStored) (pack : Fin (width + 1) ≃ NewStored)
    (choose : Switch.Past Input (Fin (width + 1)) Result OldStored → Label)
    (count : Nat) (program : Program Input (Fin (width + 1)) Result) (saved : Table Input OldStored)
    (family : Label × Input → Fin (width + 1) ≃ Fin (width + 1))
    (law : PMF (Switch.Retained Input (Fin (width + 1)) Result OldStored Label NewStored))
    (generated : generate encoder old pack choose count program saved = some (family, law)) :
    law.map (fun pair => (Switch.decode old (codecs family pack) pair).2.2) = program.run (oracle old) saved := by
  have joint := (generate_sound encoder old pack choose count program saved family law generated).2
  have projected := congrArg (fun p => p.map (fun pair => pair.2.2)) joint
  simpa only [PMF.map_comp, Function.comp_def, Switch.reference_final] using projected

end CryptoOracle.RandomOracle.Representation.GeneratedEdit
