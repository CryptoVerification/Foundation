import Foundation.Crypto.Semantics.Oracle.InteractionRules

/-! Input-dependent bijective encodings of INTERNAL function/cache values.
Public request/response history stays decoded. The masked query is defined
operationally on stored values, not by conjugating an assumed whole kernel. -/
namespace CryptoOracle.ProofEdits.Interaction.Encoding
open Foundation.Probability CryptoOracle.RandomOracle
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input]

variable (codecs : Input → Tag ≃ Tag)

def cache (table : Table Input Tag) : Table Input Tag :=
  table.map (fun entry => (entry.1, codecs entry.1 entry.2))

def state (plain : State Input Tag) : State Input Tag :=
  ⟨cache codecs plain.cache, plain.signed, plain.reverseTrace, fun input => codecs input (plain.function input)⟩

def inverse (stored : State Input Tag) : State Input Tag := state (fun input => (codecs input).symm) stored

theorem cache_lookup (table : Table Input Tag) (input : Input) :
    (cache codecs table).lookup input = (table.lookup input).map (codecs input) := by
  induction table with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨key, tag⟩ := entry
      simp only [cache, List.map_cons, List.lookup_cons]
      by_cases same : input = key
      · subst key; simp
      · simp only [beq_eq_false_iff_ne.mpr same]
        exact ih

omit [DecidableEq Input] in
theorem state_inverse (plain : State Input Tag) : inverse codecs (state codecs plain) = plain := by
  rcases plain with ⟨table, signed, history, function⟩
  have tableEq : cache (fun input => (codecs input).symm) (cache codecs table) = table := by
    simp only [cache, List.map_map, Function.comp_def, Equiv.symm_apply_apply]
    exact List.map_id _
  simp only [inverse, state, tableEq, Equiv.symm_apply_apply]

omit [DecidableEq Input] in
theorem inverse_state (stored : State Input Tag) : state codecs (inverse codecs stored) = stored := by
  simpa only [inverse, Equiv.symm_symm] using state_inverse (fun input => (codecs input).symm) stored

def equivalence : State Input Tag ≃ State Input Tag where
  toFun := state codecs
  invFun := inverse codecs
  left_inv := state_inverse codecs
  right_inv := inverse_state codecs

/-- Cache and secret are stored encoded, while responses in the public
history are decoded. Copying the old query definition would expose codes. -/
def ask (stored : State Input Tag) (message : Input) : State Input Tag :=
  match stored.cache.lookup message with
  | some tag => {stored with reverseTrace := (message, (codecs message).symm tag) :: stored.reverseTrace}
  | none => {stored with
      cache := (message, stored.function message) :: stored.cache
      reverseTrace := (message, (codecs message).symm (stored.function message)) :: stored.reverseTrace}

theorem ask_state (plain : State Input Tag) (message : Input) :
    ask codecs (state codecs plain) message = state codecs (Interaction.ask plain message) := by
  simp only [ask, state, cache_lookup]
  cases found : plain.cache.lookup message <;>
    simp [found, Interaction.ask, cache, Equiv.symm_apply_apply]

omit [DecidableEq Input] in
theorem record_state (plain : State Input Tag) (message : Input) :
    record (state codecs plain) message = state codecs (record plain message) := rfl

theorem update_state (plain : State Input Tag) (message : Input) (tag : Tag) :
    update (state codecs plain) message (codecs message tag) = state codecs (update plain message tag) := by
  have functions : Function.update (fun input => codecs input (plain.function input)) message (codecs message tag) =
      fun input => codecs input (Function.update plain.function message tag input) := by
    funext input
    by_cases same : input = message
    · subst input; simp
    · simp [Function.update_of_ne same]
  simp only [state, update, functions]

theorem known_state (seen : Finset Input) (plain : State Input Tag) :
    Known seen (state codecs plain) ↔ Known seen plain := by
  simp only [Known, state, cache_lookup, Option.map_eq_none_iff]

omit [DecidableEq Input] in
theorem coherent_state (plain : State Input Tag) : Coherent (state codecs plain) ↔ Coherent plain := by
  simp only [Coherent, TableValues, state, cache, List.mem_map]
  constructor
  · intro coherent entry member
    exact (codecs entry.1).injective (coherent _ ⟨entry, member, rfl⟩)
  · intro coherent entry member
    obtain ⟨original, present, rfl⟩ := member
    exact congrArg (codecs original.1) (coherent original present)

variable [Fintype Tag] [Nonempty Tag]

noncomputable def step : Action Input → State Input Tag → PMF (State Input Tag)
  | .query input, stored => PMF.pure (ask codecs stored input)
  | .record input, stored => PMF.pure (record stored input)
  | .refresh input, stored => (uniform Tag).map (update stored input)

noncomputable def run : List (Action Input) → State Input Tag → PMF (State Input Tag)
  | [], stored => PMF.pure stored
  | action :: tail, stored => (step codecs action stored).bind (run tail)

theorem step_state (action : Action Input) (plain : State Input Tag) :
    step codecs action (state codecs plain) = (Interaction.step action plain).map (state codecs) := by
  cases action with
  | query message => simp only [step, Interaction.step, PMF.pure_map, ask_state]
  | record message => simp only [step, Interaction.step, PMF.pure_map, record_state]
  | refresh message =>
      simp only [step, Interaction.step, resample, PMF.map_comp, Function.comp_def]
      have uniform := uniform_map_equiv (codecs message)
      conv_lhs => rw [← uniform, PMF.map_comp]
      simp only [Function.comp_def, update_state]

theorem run_state (word : List (Action Input)) (plain : State Input Tag) :
    run codecs word (state codecs plain) = (Interaction.run word plain).map (state codecs) := by
  induction word generalizing plain with
  | nil => simp [run, Interaction.run, PMF.pure_map]
  | cons action tail ih =>
      simp only [run, Interaction.run, step_state, PMF.bind_map, PMF.map_bind, Function.comp_def, ih]

/-- Recover the full plain-state distribution, including public history. -/
theorem run_inverse (word : List (Action Input)) (stored : State Input Tag) :
    (run codecs word stored).map (inverse codecs) = Interaction.run word (inverse codecs stored) := by
  conv_lhs => rw [← inverse_state codecs stored, run_state]
  simp only [PMF.map_comp, Function.comp_def, state_inverse]
  exact PMF.map_id _

/-- A representation change is local to the semantics: every old kernel
equality transports by ordinary equality congruence. No diagrams are inputs. -/
theorem transport {first second : List (Action Input)}
    (equal : ∀ plain : State Input Tag, Interaction.run first plain = Interaction.run second plain)
    (stored : State Input Tag) : run codecs first stored = run codecs second stored := by
  rw [← inverse_state codecs stored, run_state, run_state, equal]

/-- Change between two independently chosen internal encodings while
retaining the same public request/response history. -/
def recode (next : Input → Tag ≃ Tag) (stored : State Input Tag) : State Input Tag := state next (inverse codecs stored)

theorem recode_run (next : Input → Tag ≃ Tag) (word : List (Action Input)) (stored : State Input Tag) :
    (run codecs word stored).map (recode codecs next) = run next word (recode codecs next stored) := by
  rw [recode, run_state]
  change (run codecs word stored).map (state next ∘ inverse codecs) = _
  rw [← PMF.map_comp, run_inverse]

/-- Public responses retain their original values under internal encoding. -/
theorem public_history (word : List (Action Input)) (plain : State Input Tag) :
    (run codecs word (state codecs plain)).map State.reverseTrace =
      (Interaction.run word plain).map State.reverseTrace := by
  rw [run_state, PMF.map_comp]
  rfl

omit [DecidableEq Input] [Fintype Tag] [Nonempty Tag] in
theorem recode_identity (stored : State Input Tag) : recode codecs codecs stored = stored :=
  inverse_state codecs stored

omit [DecidableEq Input] [Fintype Tag] [Nonempty Tag] in
theorem recode_compose (middle last : Input → Tag ≃ Tag) (stored : State Input Tag) :
    recode middle last (recode codecs middle stored) = recode codecs last stored := by
  simp only [recode, state_inverse]

end CryptoOracle.ProofEdits.Interaction.Encoding
