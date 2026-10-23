import Foundation.Crypto.Semantics.Oracle.Refresh

/-! Explicit shared game state for cache lookup, history recording and
proof-only refresh of a secret-function coordinate. Queries retain every
actual response in reverse chronological order. A syntactic scan tracks
which coordinates have been exposed; refresh after exposure is rejected.
No native execution-time claim is attached to these semantic operations.
-/
namespace CryptoOracle.ProofEdits.Interaction
open Foundation.Probability CryptoOracle.RandomOracle
set_option backward.isDefEq.respectTransparency false

structure State (Input Tag : Type) where
  cache : Table Input Tag
  signed : List Input
  reverseTrace : List (Input × Tag)
  function : Input → Tag

inductive Action (Input : Type) where
  | query : Input → Action Input
  | record : Input → Action Input
  | refresh : Input → Action Input
  deriving DecidableEq

def queryCount (word : List (Action Input)) : Nat := word.countP (fun action => match action with | .query _ => true | _ => false)
def recordCount (word : List (Action Input)) : Nat := word.countP (fun action => match action with | .record _ => true | _ => false)
def drawCount (word : List (Action Input)) : Nat := word.countP (fun action => match action with | .refresh _ => true | _ => false)

variable {Input Tag : Type} [DecidableEq Input]

def record (state : State Input Tag) (message : Input) : State Input Tag :=
  { state with signed := state.signed ++ [message] }

def ask (state : State Input Tag) (message : Input) : State Input Tag :=
  match state.cache.lookup message with
  | some tag => { state with reverseTrace := (message, tag) :: state.reverseTrace }
  | none =>
      { state with
        cache := (message, state.function message) :: state.cache
        reverseTrace := (message, state.function message) :: state.reverseTrace }

def update (state : State Input Tag) (message : Input) (tag : Tag) : State Input Tag :=
  { state with function := Function.update state.function message tag }

def Known (seen : Finset Input) (state : State Input Tag) : Prop :=
  ∀ input, state.cache.lookup input = none ↔ input ∉ seen

def Coherent (state : State Input Tag) : Prop := TableValues state.function state.cache

theorem known_cache (state : State Input Tag) : Known (state.cache.map Prod.fst).toFinset state := by
  intro input
  simp [List.lookup_eq_none_iff]
  constructor
  · intro absent tag member
    exact absent input tag member rfl
  · intro absent key tag member same
    subst key
    exact absent tag member

def scan : Finset Input → List (Action Input) → Option (Finset Input)
  | seen, [] => some seen
  | seen, .query input :: tail => scan (insert input seen) tail
  | seen, .record _ :: tail => scan seen tail
  | seen, .refresh input :: tail => if input ∈ seen then none else scan seen tail

theorem record_known (seen : Finset Input) (state : State Input Tag) (message : Input)
    (known : Known seen state) : Known seen (record state message) := known

omit [DecidableEq Input] in
theorem record_coherent (state : State Input Tag) (message : Input)
    (coherent : Coherent state) : Coherent (record state message) := coherent

theorem ask_known (seen : Finset Input) (state : State Input Tag) (message : Input)
    (known : Known seen state) : Known (insert message seen) (ask state message) := by
  intro input
  by_cases same : input = message
  · subst input
    cases cached : state.cache.lookup message <;> simp [ask, cached]
  · cases cached : state.cache.lookup message <;>
      simpa only [ask, cached, List.lookup_cons, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true,
        if_false, Finset.mem_insert, same, false_or] using known input

theorem ask_coherent (state : State Input Tag) (message : Input)
    (coherent : Coherent state) : Coherent (ask state message) := by
  cases cached : state.cache.lookup message with
  | some tag => simpa only [ask, cached, Coherent] using coherent
  | none =>
      simp only [Coherent, ask, cached]
      intro entry member
      rcases List.mem_cons.mp member with rfl | old
      · rfl
      · exact coherent entry old

theorem update_known (seen : Finset Input) (state : State Input Tag) (message : Input) (tag : Tag)
    (known : Known seen state) : Known seen (update state message tag) := known

theorem update_coherent (state : State Input Tag) (message : Input) (tag : Tag)
    (coherent : Coherent state) (fresh : state.cache.lookup message = none) :
    Coherent (update state message tag) := by
  intro entry member
  have different : entry.1 ≠ message := by
    intro same
    have excluded := List.lookup_eq_none_iff.mp fresh entry member
    simp [same] at excluded
  change entry.2 = Function.update state.function message tag entry.1
  exact (coherent entry member).trans (Function.update_of_ne different tag state.function).symm

theorem ask_record (state : State Input Tag) (request message : Input) :
    ask (record state message) request = record (ask state request) message := by
  cases cached : state.cache.lookup request <;> simp [ask, record, cached]

theorem update_record (state : State Input Tag) (request message : Input) (tag : Tag) :
    update (record state message) request tag = record (update state request tag) message := rfl

theorem ask_update (state : State Input Tag) (request message : Input) (tag : Tag)
    (different : request ≠ message) :
    ask (update state message tag) request = update (ask state request) message tag := by
  cases cached : state.cache.lookup request <;>
    simp [ask, update, cached, Function.update_of_ne different]

theorem ask_lookup_other (state : State Input Tag) (request input : Input) (different : input ≠ request) :
    (ask state request).cache.lookup input = state.cache.lookup input := by
  cases cached : state.cache.lookup request <;>
    simp [ask, cached, List.lookup_cons, beq_eq_false_iff_ne.mpr different]

theorem ask_signed (state : State Input Tag) (message : Input) : (ask state message).signed = state.signed := by
  cases cached : state.cache.lookup message <;> simp [ask, cached]

variable [Fintype Tag] [Nonempty Tag]

noncomputable def resample (state : State Input Tag) (message : Input) : PMF (State Input Tag) :=
  (uniform Tag).map (update state message)

noncomputable def step : Action Input → State Input Tag → PMF (State Input Tag)
  | .query input, state => PMF.pure (ask state input)
  | .record input, state => PMF.pure (record state input)
  | .refresh input, state => resample state input

noncomputable def run : List (Action Input) → State Input Tag → PMF (State Input Tag)
  | [], state => PMF.pure state
  | action :: tail, state => (step action state).bind (run tail)

theorem run_append (first second : List (Action Input)) (state : State Input Tag) :
    run (first ++ second) state = (run first state).bind (run second) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons action tail ih =>
      simp only [List.cons_append, run, PMF.bind_bind]
      exact congrArg (PMF.bind (step action state)) (funext ih)

omit [Fintype Tag] [Nonempty Tag] in
theorem ask_eager (state : State Input Tag) (message : Input) :
    (eager state.function state.cache message).map (fun answer =>
      { state with cache := answer.1, reverseTrace := (message, answer.2) :: state.reverseTrace }) =
      PMF.pure (ask state message) := by
  cases cached : state.cache.lookup message <;> simp [eager, ask, cached, PMF.pure_map]

theorem run_valid (word : List (Action Input)) (seen finalSeen : Finset Input)
    (valid : scan seen word = some finalSeen) (state final : State Input Tag)
    (known : Known seen state) (coherent : Coherent state) (supported : final ∈ (run word state).support) :
    Known finalSeen final ∧ Coherent final := by
  induction word generalizing seen finalSeen state final with
  | nil =>
      simp only [scan, Option.some.injEq] at valid
      subst finalSeen
      rw [run, PMF.mem_support_pure_iff] at supported
      subst final
      exact ⟨known, coherent⟩
  | cons action tail ih =>
      rw [run, PMF.mem_support_bind_iff] at supported
      obtain ⟨next, selected, supported⟩ := supported
      cases action with
      | query message =>
          rw [step, PMF.mem_support_pure_iff] at selected
          subst next
          exact ih _ _ valid _ final (ask_known seen state message known) (ask_coherent state message coherent) supported
      | record message =>
          rw [step, PMF.mem_support_pure_iff] at selected
          subst next
          exact ih seen finalSeen valid (record state message) final known coherent supported
      | refresh message =>
          simp only [scan] at valid
          split at valid
          · cases valid
          · rename_i absent
            rw [step, resample, PMF.mem_support_map_iff] at selected
            obtain ⟨tag, _, rfl⟩ := selected
            exact ih seen finalSeen valid (update state message tag) final known
              (update_coherent state message tag coherent ((known message).mpr absent)) supported

end CryptoOracle.ProofEdits.Interaction
