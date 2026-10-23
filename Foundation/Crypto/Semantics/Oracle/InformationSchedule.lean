import Foundation.Crypto.Semantics.Probability.Facts

/-! Proof-only schedules of information revelation and private commitments.
A policy's input type contains only its declared dependencies. Unavailable
values are not read; accepted scans ensure all required inputs are available.
Revelation is a visibility annotation, not an oracle-call instruction. -/
namespace CryptoOracle.InformationSchedule
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

inductive Action (Variable Key : Type) where
  | reveal : Variable → Action Variable Key
  | commit : Key → Action Variable Key
  deriving DecidableEq

structure State (Variable Key Choice : Type) where
  hidden : Variable → Bool
  seen : Finset Variable
  chosen : Key → Option Choice

variable {Variable Key Choice : Type} [DecidableEq Variable] [DecidableEq Key]
variable (signature : Key → Finset Variable)

def view (state : State Variable Key Choice) (key : Key) : {v // v ∈ signature key} → Bool :=
  fun input => if input.val ∈ state.seen then state.hidden input.val else false

def reveal (state : State Variable Key Choice) (input : Variable) : State Variable Key Choice :=
  {state with seen := insert input state.seen}

def commit (state : State Variable Key Choice) (key : Key) (choice : Choice) : State Variable Key Choice :=
  {state with chosen := Function.update state.chosen key (some choice)}

variable (policy : (key : Key) → ({v // v ∈ signature key} → Bool) → PMF Choice)

noncomputable def step : Action Variable Key → State Variable Key Choice → PMF (State Variable Key Choice)
  | .reveal input, state => PMF.pure (reveal state input)
  | .commit key, state => (policy key (view signature state key)).map (commit state key)

noncomputable def run : List (Action Variable Key) → State Variable Key Choice → PMF (State Variable Key Choice)
  | [], state => PMF.pure state
  | action :: rest, state => (step signature policy action state).bind (run rest)

def scan : Finset Variable → List (Action Variable Key) → Option (Finset Variable)
  | seen, [] => some seen
  | seen, .reveal input :: rest => scan (insert input seen) rest
  | seen, .commit key :: rest => if signature key ⊆ seen then scan seen rest else none

def independent : Action Variable Key → Action Variable Key → Bool
  | .reveal _, .reveal _ => true
  | .reveal input, .commit key | .commit key, .reveal input => decide (input ∉ signature key)
  | .commit first, .commit second => decide (first ≠ second)

omit [DecidableEq Key] in
theorem view_available (state : State Variable Key Choice) (key : Key)
    (available : signature key ⊆ state.seen) :
    view signature state key = fun input => state.hidden input.val := by
  funext input
  simp only [view, if_pos (available input.property)]

omit [DecidableEq Key] in
/-- A fixed registered policy sees no difference between states which agree
on the currently visible hidden values. Existing commitments are not inputs. -/
theorem view_noninterference (first second : State Variable Key Choice) (key : Key)
    (seenEq : first.seen = second.seen)
    (visibleEq : ∀ input ∈ first.seen, first.hidden input = second.hidden input) :
    view signature first key = view signature second key := by
  funext dependency
  by_cases visible : dependency.val ∈ first.seen
  · simp only [view, ← seenEq, if_pos visible, visibleEq dependency.val visible]
  · simp only [view, ← seenEq, if_neg visible]

omit [DecidableEq Key] in
theorem view_reveal (state : State Variable Key Choice) (key : Key) (input : Variable)
    (absent : input ∉ signature key) :
    view signature (reveal state input) key = view signature state key := by
  funext dependency
  have different : dependency.val ≠ input := by
    intro same
    exact absent (same ▸ dependency.property)
  simp [view, reveal, different]

omit [DecidableEq Key] in
theorem subset_reveal (seen : Finset Variable) (key : Key) (input : Variable)
    (absent : input ∉ signature key) :
    signature key ⊆ insert input seen ↔ signature key ⊆ seen := by
  constructor
  · intro included input member
    rcases Finset.mem_insert.mp (included member) with same | present
    · exact False.elim (absent (same ▸ member))
    · exact present
  · exact fun included => Finset.Subset.trans included (Finset.subset_insert _ _)

theorem scan_exchange (seen : Finset Variable) (first second : Action Variable Key)
    (allowed : independent signature first second = true) (rest : List (Action Variable Key)) :
    scan signature seen (first :: second :: rest) = scan signature seen (second :: first :: rest) := by
  cases first with
  | reveal input =>
      cases second with
      | reveal other => simp only [scan, Finset.insert_comm]
      | commit key =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp only [scan, subset_reveal signature seen key input allowed]
  | commit key =>
      cases second with
      | reveal input =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp only [scan, subset_reveal signature seen key input allowed]
      | commit other =>
          by_cases left : signature key ⊆ seen <;> by_cases right : signature other ⊆ seen <;>
            simp [scan, left, right]

theorem reveal_commit (state : State Variable Key Choice) (input : Variable) (key : Key)
    (absent : input ∉ signature key) :
    (step signature policy (.reveal input) state).bind (step signature policy (.commit key)) =
      (step signature policy (.commit key) state).bind (step signature policy (.reveal input)) := by
  simp only [step, PMF.pure_bind, view_reveal signature state key input absent, PMF.bind_map]
  rfl

theorem commit_commit (state : State Variable Key Choice) (first second : Key) (different : first ≠ second) :
    (step signature policy (.commit first) state).bind (step signature policy (.commit second)) =
      (step signature policy (.commit second) state).bind (step signature policy (.commit first)) := by
  have views (key other : Key) (choice : Choice) :
      view signature (commit state key choice) other = view signature state other := rfl
  simp only [step, PMF.bind_map, Function.comp_def, views]
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext secondChoice
  congr 1
  funext firstChoice
  congr 1
  unfold commit
  congr 1
  exact Function.update_comm different _ _ _

theorem step_exchange (first second : Action Variable Key)
    (allowed : independent signature first second = true) (state : State Variable Key Choice) :
    (step signature policy first state).bind (step signature policy second) =
      (step signature policy second state).bind (step signature policy first) := by
  cases first with
  | reveal input =>
      cases second with
      | reveal other => simp [step, reveal, Finset.insert_comm]
      | commit key =>
          simp only [independent, decide_eq_true_eq] at allowed
          exact reveal_commit signature policy state input key allowed
  | commit key =>
      cases second with
      | reveal input =>
          simp only [independent, decide_eq_true_eq] at allowed
          exact (reveal_commit signature policy state input key allowed).symm
      | commit other =>
          simp only [independent, decide_eq_true_eq] at allowed
          exact commit_commit signature policy state key other allowed

/-- A successful scan tracks the actual visibility of every supported
execution, not only an unrelated syntactic set. -/
theorem run_seen (word : List (Action Variable Key)) (state final : State Variable Key Choice)
    (available : Finset Variable) (checked : scan signature state.seen word = some available)
    (supported : final ∈ (run signature policy word state).support) : final.seen = available := by
  induction word generalizing state with
  | nil =>
      simp only [scan, Option.some.injEq] at checked
      rw [run, PMF.mem_support_pure_iff] at supported
      subst final
      exact checked
  | cons action rest ih =>
      cases action with
      | reveal input =>
          rw [run, step, PMF.pure_bind] at supported
          exact ih (reveal state input) checked supported
      | commit key =>
          by_cases ready : signature key ⊆ state.seen
          · simp only [scan, if_pos ready] at checked
            rw [run, PMF.mem_support_bind_iff] at supported
            obtain ⟨next, selected, supported⟩ := supported
            rw [step, PMF.mem_support_map_iff] at selected
            obtain ⟨choice, _, rfl⟩ := selected
            exact ih (commit state key choice) checked supported
          · simp [scan, ready] at checked

end CryptoOracle.InformationSchedule
