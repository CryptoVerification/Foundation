import Foundation.Crypto.Semantics.Oracle.QueryPrefix

/-! Operational representation changes at an extracted execution boundary.
The new codec is selected from the ACTUAL old prefix. Its label and the prefix
are retained; the cache is recoded and the original continuation is resumed.
This is an ordinary probabilistic state-transport theorem, not a new physical
machine implementation or a claim of exclusive higher-dimensional power. -/
namespace CryptoOracle.RandomOracle.Representation.Switch
open Foundation.Probability
variable {Input Response OldStored NewStored Result Label : Type}

def recode (old : Input → Response ≃ OldStored) (new : Input → Response ≃ NewStored)
    (saved : Table Input OldStored) : Table Input NewStored :=
  table (fun input => (old input).symm.trans (new input)) saved

theorem recode_roundtrip (old : Input → Response ≃ OldStored) (new : Input → Response ≃ NewStored)
    (saved : Table Input OldStored) : recode new old (recode old new saved) = saved := by
  simp only [recode, table, List.map_map, Function.comp_def, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  exact List.map_id _

theorem recode_encoded (old : Input → Response ≃ OldStored) (new : Input → Response ≃ NewStored)
    (plain : Table Input Response) : recode old new (table old plain) = table new plain := by
  simp only [recode, table, List.map_map, Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem recode_comp {MiddleStored : Type} (old : Input → Response ≃ OldStored)
    (middle : Input → Response ≃ MiddleStored) (new : Input → Response ≃ NewStored)
    (saved : Table Input OldStored) :
    recode middle new (recode old middle saved) = recode old new saved := by
  simp only [recode, table, List.map_map, Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply]

variable [DecidableEq Input] [Fintype Response] [Nonempty Response]

theorem step_recode (old : Input → Response ≃ OldStored) (new : Input → Response ≃ NewStored)
    (saved : Table Input OldStored) (input : Input) :
    (oracle old saved input).map (fun answer => (recode old new answer.1, answer.2)) =
      oracle new (recode old new saved) input := by
  simp only [oracle, recode, lookup]
  cases found : saved.lookup input <;>
    simp [table, PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem run_recode (old : Input → Response ≃ OldStored) (new : Input → Response ≃ NewStored)
    (program : Program Input Response Result) (saved : Table Input OldStored) :
    (program.run (oracle old) saved).map (Program.mapState (recode old new)) =
      program.run (oracle new) (recode old new saved) := by
  exact Program.run_state_map (recode old new) (oracle old) (oracle new) (step_recode old new) program saved

abbrev Past (Input Response Result OldStored : Type) :=
  Outcome Input Response (Program Input Response Result) (Table Input OldStored)

abbrev Retained (Input Response Result OldStored Label Stored : Type) :=
  Past Input Response Result OldStored × Label × Outcome Input Response Result (Table Input Stored)

def encode (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (pair : Retained Input Response Result OldStored Label OldStored) :
    Retained Input Response Result OldStored Label NewStored :=
  (pair.1, pair.2.1, Program.mapState (recode old (codecs pair.2.1)) pair.2.2)

def decode (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (pair : Retained Input Response Result OldStored Label NewStored) :
    Retained Input Response Result OldStored Label OldStored :=
  (pair.1, pair.2.1, Program.mapState (recode (codecs pair.2.1) old) pair.2.2)

omit [DecidableEq Input] [Fintype Response] [Nonempty Response] in
theorem decode_encode (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (pair : Retained Input Response Result OldStored Label OldStored) : decode old codecs (encode old codecs pair) = pair := by
  rcases pair with ⟨past, label, result, saved, trace⟩
  simp only [decode, encode, Program.mapState, recode_roundtrip]

noncomputable def reference (old : Input → Response ≃ OldStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    PMF (Retained Input Response Result OldStored Label OldStored) :=
  ((Program.pauseAfter count program).run (oracle old) saved).bind fun past =>
    (past.result.run (oracle old) past.state).map fun last =>
      (past, choose past, {last with trace := past.trace ++ last.trace})

/-- Executing the changed oracle, not just mapping an already completed run. -/
noncomputable def joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    PMF (Retained Input Response Result OldStored Label NewStored) :=
  ((Program.pauseAfter count program).run (oracle old) saved).bind fun past =>
    (past.result.run (oracle (codecs (choose past))) (recode old (codecs (choose past)) past.state)).map fun last =>
      (past, choose past, {last with trace := past.trace ++ last.trace})

theorem operational_joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    joint old codecs choose count program saved =
      (reference old choose count program saved).map (encode old codecs) := by
  simp only [joint, reference, PMF.map_bind]
  congr 1
  funext past
  rw [← run_recode old (codecs (choose past)) past.result past.state, PMF.map_comp, PMF.map_comp]
  rfl

theorem decoded_joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose count program saved).map (decode old codecs) =
      reference old choose count program saved := by
  rw [operational_joint, PMF.map_comp]
  have inverse : decode old codecs ∘ encode old codecs =
      (id : Retained Input Response Result OldStored Label OldStored → _) := by
    funext pair
    exact decode_encode old codecs pair
  rw [inverse, PMF.map_id]

theorem prefix_selection (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose count program saved).map (fun pair => (pair.1, pair.2.1)) =
      ((Program.pauseAfter count program).run (oracle old) saved).map (fun past => (past, choose past)) := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (((Program.pauseAfter count program).run (oracle old) saved).bind fun past =>
    (past.result.run (oracle (codecs (choose past))) (recode old (codecs (choose past)) past.state)).map
      (Function.const _ (past, choose past))) = _
  simp only [PMF.map_const]
  rfl

theorem reference_final (old : Input → Response ≃ OldStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (reference old choose count program saved).map (fun pair => pair.2.2) = program.run (oracle old) saved := by
  simp only [reference, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact Program.pauseAfter_continuation count program (oracle old) saved

theorem decoded_final (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose count program saved).map (fun pair => (decode old codecs pair).2.2) =
      program.run (oracle old) saved := by
  have law := congrArg (fun p => p.map (fun pair => pair.2.2))
    (decoded_joint old codecs choose count program saved)
  simpa only [PMF.map_comp, Function.comp_def, reference_final] using law

theorem decoded_continuation {Next : Type} (old : Input → Response ≃ OldStored)
    (codecs : Label → Input → Response ≃ NewStored) (choose : Past Input Response Result OldStored → Label)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored)
    (next : Retained Input Response Result OldStored Label OldStored → PMF Next) :
    (joint old codecs choose count program saved).bind (fun pair => next (decode old codecs pair)) =
      (reference old choose count program saved).bind next := by
  have law := congrArg (fun p => p.bind next) (decoded_joint old codecs choose count program saved)
  simpa only [PMF.bind_map, Function.comp_def] using law

end CryptoOracle.RandomOracle.Representation.Switch
