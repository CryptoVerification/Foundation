import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Stable chronological labels for the existing lazy random oracle. Labels
are assigned once to sampled entries; erasing labels preserves full adaptive
outcomes. This representation alone does not establish hidden-value independence
or authorize resampling. Hash latent-value experiments require those separately. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

structure IndexedTable (Input Output : Type) where
  labels : Table Input Nat
  values : List Output

namespace IndexedTable
variable {Input Output Result : Type} [DecidableEq Input]

/-- Each referenced chronological label has a stored value. -/
def Valid (state : IndexedTable Input Output) : Prop :=
  ∀ entry ∈ state.labels, entry.2 < state.values.length

/-- A default only makes erasure total on malformed representations. For valid
states every referenced label has a value, so the default is irrelevant. -/
def erase (fallback : Output) (state : IndexedTable Input Output) : Table Input Output :=
  state.labels.map (fun entry => (entry.1, state.values[entry.2]?.getD fallback))

def empty : IndexedTable Input Output := ⟨[], []⟩

def insert (state : IndexedTable Input Output) (input : Input) (output : Output) :
    IndexedTable Input Output :=
  ⟨(input, state.values.length) :: state.labels, state.values ++ [output]⟩

theorem erase_lookup (fallback : Output) (state : IndexedTable Input Output) (input : Input) :
    (erase fallback state).lookup input =
      (state.labels.lookup input).map (fun label => state.values[label]?.getD fallback) := by
  rcases state with ⟨labels, values⟩
  change (labels.map (fun entry => (entry.1, values[entry.2]?.getD fallback))).lookup input =
    (labels.lookup input).map (fun label => values[label]?.getD fallback)
  induction labels with
  | nil => rfl
  | cons entry labels ih =>
      rcases entry with ⟨key, label⟩
      simp only [List.map_cons, List.lookup_cons]
      split <;> simp_all

omit [DecidableEq Input] in
theorem valid_insert (state : IndexedTable Input Output) (valid : state.Valid)
    (input : Input) (output : Output) : (state.insert input output).Valid := by
  intro entry hm
  rcases List.mem_cons.mp hm with rfl | hm
  · simp [insert]
  · have old := valid entry hm
    simp only [insert, List.length_append, List.length_singleton]
    omega

omit [DecidableEq Input] in
theorem erase_insert (fallback : Output) (state : IndexedTable Input Output) (valid : state.Valid)
    (input : Input) (output : Output) :
    erase fallback (state.insert input output) = (input, output) :: erase fallback state := by
  simp only [erase, insert, List.map_cons]
  congr 1
  · simp
  · apply List.map_congr_left
    intro entry member
    rw [List.getElem?_append_left (valid entry member)]

omit [DecidableEq Input] in
/-- Defaults do not affect decoding of any well-formed indexed table. -/
theorem erase_fallback (left right : Output) (state : IndexedTable Input Output) (valid : state.Valid) :
    erase left state = erase right state := by
  apply List.map_congr_left
  intro entry member
  simp only [List.getElem?_eq_getElem (valid entry member), Option.getD_some]

variable [Fintype Output] [Nonempty Output]

/-- The oracle still samples on the first actual query. Output labels are
private storage, and are never returned as adversary responses. -/
noncomputable def oracle (fallback : Output) : Oracle Input Output (IndexedTable Input Output) :=
  fun state input => match state.labels.lookup input with
  | some label => PMF.pure (state, state.values[label]?.getD fallback)
  | none => (uniform Output).map (fun output => (state.insert input output, output))

theorem step_valid (fallback : Output) (state : IndexedTable Input Output) (valid : state.Valid)
    (input : Input) (answer : IndexedTable Input Output × Output)
    (support : answer ∈ (oracle fallback state input).support) : answer.1.Valid := by
  cases cached : state.labels.lookup input with
  | some label =>
      rw [oracle, cached, PMF.mem_support_pure_iff] at support
      subst answer
      exact valid
  | none =>
      rw [oracle, cached, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      exact valid_insert state valid input output

/-- Erasure commutes with one genuine lazy-sampling transition. -/
theorem step_erase (fallback : Output) (state : IndexedTable Input Output) (valid : state.Valid)
    (input : Input) :
    (oracle fallback state input).map (fun answer => (erase fallback answer.1, answer.2)) =
      RandomOracle.oracle (erase fallback state) input := by
  cases cached : state.labels.lookup input with
  | some label =>
      simp [oracle, RandomOracle.oracle, erase_lookup, cached, PMF.pure_map]
  | none =>
      simp [oracle, RandomOracle.oracle, erase_lookup, cached, PMF.map_comp,
        Function.comp_def, erase_insert fallback state valid]

/-- Stable labels implement the existing oracle for every adaptive program,
with the same result, decoded cache and complete public query transcript. -/
theorem run_erase (fallback : Output) (program : Program Input Output Result)
    (state : IndexedTable Input Output) (valid : state.Valid) :
    (program.run (oracle fallback) state).map (Program.mapState (erase fallback)) =
      program.run RandomOracle.oracle (erase fallback state) :=
  Program.run_state_map_of_invariant (erase fallback) (oracle fallback) RandomOracle.oracle Valid
    (step_valid fallback) (step_erase fallback) program state valid

/-- All referenced labels remain allocated throughout an adaptive run. -/
theorem run_valid (fallback : Output) (program : Program Input Output Result)
    (state : IndexedTable Input Output) (valid : state.Valid)
    (out : Outcome Input Output Result (IndexedTable Input Output))
    (support : out ∈ (program.run (oracle fallback) state).support) : out.state.Valid :=
  Program.run_preserves (oracle fallback) Valid (step_valid fallback) program state valid out support

/-- The response has a stored chronological label with exactly that value. -/
theorem step_records (fallback : Output) (state : IndexedTable Input Output) (valid : state.Valid)
    (input : Input) (answer : IndexedTable Input Output × Output)
    (support : answer ∈ (oracle fallback state input).support) :
    ∃ label, answer.1.labels.lookup input = some label ∧ answer.1.values[label]? = some answer.2 := by
  cases cached : state.labels.lookup input with
  | some label =>
      rw [oracle, cached, PMF.mem_support_pure_iff] at support
      subst answer
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp cached
      have member : (input, label) ∈ state.labels := by rw [he]; simp
      have bound := valid (input, label) member
      refine ⟨label, cached, ?_⟩
      simp [List.getElem?_eq_getElem bound]
  | none =>
      rw [oracle, cached, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      exact ⟨state.values.length, by simp [insert], by simp [insert]⟩

/-- Existing chronological coordinates retain their values after a step. -/
theorem step_values_extend (fallback : Output) (state : IndexedTable Input Output)
    (input : Input) (answer : IndexedTable Input Output × Output)
    (support : answer ∈ (oracle fallback state input).support) :
    ∃ added : List Output, answer.1.values = state.values ++ added ∧ added.length ≤ 1 := by
  cases cached : state.labels.lookup input with
  | some label =>
      rw [oracle, cached, PMF.mem_support_pure_iff] at support
      subst answer
      exact ⟨[], by simp, by simp⟩
  | none =>
      rw [oracle, cached, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      exact ⟨[output], rfl, le_rfl⟩

/-- Query bounds control the number of allocated chronological values. This
counts stored outputs, not encoded machine space or elapsed execution time. -/
theorem run_values_extend (fallback : Output) (program : Program Input Output Result)
    (state : IndexedTable Input Output)
    (out : Outcome Input Output Result (IndexedTable Input Output))
    (support : out ∈ (program.run (oracle fallback) state).support) :
    ∃ added : List Output, out.state.values = state.values ++ added ∧ added.length ≤ out.trace.length := by
  induction program generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨[], by simp, le_rfl⟩
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state out ht
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      obtain ⟨added, he, bound⟩ := step_values_extend fallback state input answer ha
      obtain ⟨later, hl, length⟩ := ih answer.2 answer.1 tail ht
      refine ⟨added ++ later, ?_, ?_⟩
      · simp only
        rw [hl, he, List.append_assoc]
      · simp only [List.length_append, List.length_cons]
        omega

theorem bounded_values (fallback : Output) {program : Program Input Output Result} {q : Nat}
    (bound : program.BoundedQueries q) (state : IndexedTable Input Output)
    (out : Outcome Input Output Result (IndexedTable Input Output))
    (support : out ∈ (program.run (oracle fallback) state).support) :
    out.state.values.length ≤ state.values.length + q := by
  obtain ⟨added, he, length⟩ := run_values_extend fallback program state out support
  have calls := bound.trace_length_le (oracle fallback) state out support
  rw [he, List.length_append]
  omega

/-- Every actual response in a transcript has a stable allocated coordinate
in the final indexed table. This includes internal calls of a hash evaluation. -/
theorem run_response_label (fallback : Output) (program : Program Input Output Result)
    (state : IndexedTable Input Output) (valid : state.Valid)
    (out : Outcome Input Output Result (IndexedTable Input Output))
    (support : out ∈ (program.run (oracle fallback) state).support)
    (input : Input) (output : Output) (member : (input, output) ∈ out.trace) :
    ∃ label, out.state.labels.lookup input = some label ∧ out.state.values[label]? = some output := by
  have erasedSupport : Program.mapState (erase fallback) out ∈
      (program.run RandomOracle.oracle (erase fallback state)).support := by
    rw [← run_erase fallback program state valid, PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  have records := (RandomOracle.run program (erase fallback state)
    (Program.mapState (erase fallback) out) erasedSupport).2.1 (input, output) member
  change (erase fallback out.state).lookup input = some output at records
  rw [erase_lookup] at records
  cases cached : out.state.labels.lookup input with
  | none => simp [cached] at records
  | some label =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp cached
      have entry : (input, label) ∈ out.state.labels := by rw [he]; simp
      have bound := run_valid fallback program state valid out support (input, label) entry
      simp only [cached, Option.map_some, Option.some.injEq,
        List.getElem?_eq_getElem bound, Option.getD_some] at records
      exact ⟨label, rfl, by simp [List.getElem?_eq_getElem bound, records]⟩

end IndexedTable
end CryptoOracle.RandomOracle
