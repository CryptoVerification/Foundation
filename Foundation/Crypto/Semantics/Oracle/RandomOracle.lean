import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Crypto.Semantics.Probability.Facts

/-! Lazy sampling inside the existing adaptive oracle semantics. Only the
response alphabet is finite. The input alphabet need not be finite or countable.
The association list stores exactly the entries sampled so far; it is not a
uniformly sampled infinite function. There is no programming operation. -/
namespace CryptoOracle.RandomOracle

set_option backward.isDefEq.respectTransparency false

open Foundation.Probability
open scoped ENNReal

variable {Input Output Result : Type} [DecidableEq Input]
  [Fintype Output] [Nonempty Output]

abbrev Table (Input Output : Type) := List (Input × Output)

/-- The first recorded value is returned on every repeated request. -/
noncomputable def oracle : Oracle Input Output (Table Input Output) :=
  fun table input => match table.lookup input with
    | some output => PMF.pure (table, output)
    | none => (uniform Output).map fun output => ((input, output) :: table, output)

theorem known (table : Table Input Output) (input : Input) (output : Output)
    (h : table.lookup input = some output) :
    oracle table input = PMF.pure (table, output) := by
  simp [oracle, h]

theorem fresh (table : Table Input Output) (input : Input)
    (h : table.lookup input = none) :
    oracle table input =
      (uniform Output).map (fun output => ((input, output) :: table, output)) := by
  simp [oracle, h]

/-- Uniformity conditional on any fixed reachable table and fresh input.
In particular, the input can be chosen from earlier responses. -/
theorem fresh_response (table : Table Input Output) (input : Input)
    (h : table.lookup input = none) :
    (oracle table input).map Prod.snd = uniform Output := by
  rw [fresh table input h, PMF.map_comp]
  change (uniform Output).map id = uniform Output
  exact PMF.map_id _

theorem fresh_guess (table : Table Input Output) (input : Input) (guess : Output)
    (h : table.lookup input = none) :
    eventProb ((oracle table input).map Prod.snd) (· = guess) =
      (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  rw [fresh_response table input h]
  exact uniform_guess guess

/-- A random history may determine both the next input and the current
table. If that input is fresh on every possible history, its response law
is still uniform. This does not expose the table to the client. -/
theorem adaptive_fresh {History : Type} (history : ProbComp History)
    (table : History → Table Input Output) (input : History → Input)
    (h : ∀ past, (table past).lookup (input past) = none) :
    (history.bind (fun past => oracle (table past) (input past))).map Prod.snd =
      uniform Output := by
  rw [PMF.map_bind]
  simp_rw [fresh_response _ _ (h _)]
  simp

/-- Joint independence of a fresh response and the complete earlier history.
Freshness is required only on histories in the distribution's support. This
is stronger than a statement merely about the response marginal. -/
theorem adaptive_fresh_joint {History : Type} (history : ProbComp History)
    (table : History → Table Input Output) (input : History → Input)
    (h : ∀ past ∈ history.support, (table past).lookup (input past) = none) :
    history.bind (fun past =>
      (oracle (table past) (input past)).map (fun answer => (past, answer.2))) =
    history.bind (fun past => (uniform Output).map (fun output => (past, output))) := by
  apply bind_congr_of_support
  intro past hp
  have he := congrArg (PMF.map (fun output : Output => (past, output)))
    (fresh_response (table past) (input past) (h past hp))
  simpa only [PMF.map_comp, Function.comp_def] using he

/-- Every sampled step records its answer, preserves all old answers, and
adds at most one entry. These facts do not depend on the client's identity. -/
theorem step (table : Table Input Output) (input : Input)
    (answer : Table Input Output × Output)
    (h : answer ∈ (oracle table input).support) :
    answer.1.lookup input = some answer.2 ∧
    (∀ x y, table.lookup x = some y → answer.1.lookup x = some y) ∧
    answer.1.length ≤ table.length + 1 := by
  cases ht : table.lookup input with
  | some output =>
      rw [known table input output ht, PMF.mem_support_pure_iff] at h
      subst answer
      exact ⟨ht, fun _ _ hx => hx, Nat.le_succ _⟩
  | none =>
      rw [fresh table input ht, PMF.mem_support_map_iff] at h
      obtain ⟨output, _, rfl⟩ := h
      refine ⟨by simp, ?_, by simp⟩
      intro x y hx
      have hne : x ≠ input := by
        intro he
        subst x
        rw [ht] at hx
        cases hx
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hne, hx]

/-- A single step records only the actual request and preserves earlier entries. -/
theorem step_entries (table : Table Input Output) (input : Input)
    (answer : Table Input Output × Output)
    (h : answer ∈ (oracle table input).support) :
    answer.1 ⊆ (input, answer.2) :: table := by
  cases he : table.lookup input with
  | some value =>
      rw [known table input value he, PMF.mem_support_pure_iff] at h
      subst answer
      exact fun _ hm => List.mem_cons_of_mem _ hm
  | none =>
      rw [fresh table input he, PMF.mem_support_map_iff] at h
      obtain ⟨value, _, rfl⟩ := h
      exact List.Subset.refl _

/-- Arbitrary adaptive execution preserves old entries, agrees with every
public response, and stores no more new entries than actual oracle calls. -/
theorem run (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (h : out ∈ (program.run oracle table).support) :
    (∀ x y, table.lookup x = some y → out.state.lookup x = some y) ∧
    (∀ entry ∈ out.trace, out.state.lookup entry.1 = some entry.2) ∧
    out.state.length ≤ table.length + out.trace.length := by
  induction program generalizing table out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at h
      subst out
      exact ⟨fun _ _ hx => hx, by simp, by simp⟩
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at h
      obtain ⟨answer, ha, h⟩ := h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨tail, ht, rfl⟩ := h
      obtain ⟨hAnswer, hOld, hLength⟩ := step table input answer ha
      obtain ⟨hKeep, hTrace, hSize⟩ := ih answer.2 answer.1 tail ht
      refine ⟨fun x y hx => hKeep x y (hOld x y hx), ?_, ?_⟩
      · intro entry he
        rcases List.mem_cons.mp he with he | he
        · subst entry
          exact hKeep input answer.2 hAnswer
        · exact hTrace entry he
      · simp only [List.length_cons]
        omega
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at h
      obtain ⟨bit, _, ht⟩ := h
      exact ih bit table out ht

/-- Each table entry comes from the initial table or an actual recorded
query. In particular, lazy sampling never fills unqueried coordinates. -/
theorem run_entries (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (h : out ∈ (program.run oracle table).support) :
    out.state ⊆ out.trace ++ table := by
  induction program generalizing table out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at h
      subst out
      simp
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at h
      obtain ⟨answer, ha, h⟩ := h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨tail, ht, rfl⟩ := h
      have hStep := step_entries table input answer ha
      intro entry hm
      have hi := ih answer.2 answer.1 tail ht hm
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ hi)
      · rcases List.mem_cons.mp (hStep hi) with hi | hi
        · subst entry
          exact List.mem_append_left _ (List.mem_cons_self ..)
        · exact List.mem_append_right _ hi
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at h
      obtain ⟨bit, _, ht⟩ := h
      exact ih bit table out ht

/-- Starting empty, an input not present in the actual transcript is still
fresh at the end, even when all earlier inputs were selected adaptively. -/
theorem unqueried_fresh (program : Program Input Output Result)
    (out : Outcome Input Output Result (Table Input Output))
    (h : out ∈ (program.run oracle []).support) (input : Input)
    (unqueried : ∀ output, (input, output) ∉ out.trace) :
    out.state.lookup input = none := by
  cases he : out.state.lookup input with
  | none => rfl
  | some output =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      have hm : (input, output) ∈ out.state := by rw [hs]; simp
      have ht := run_entries program [] out h hm
      exact False.elim (unqueried output (by simpa using ht))

/-- Different clients may choose the two calls. They share a single table. -/
theorem repeated (table : Table Input Output) (input : Input) :
    (Program.query input (fun first => Program.query input (fun second =>
      Program.done (first, second)))).run oracle table =
    (oracle table input).map (fun answer =>
      (⟨(answer.2, answer.2), answer.1, [(input, answer.2), (input, answer.2)]⟩ :
        Outcome Input Output (Output × Output) (Table Input Output))) := by
  cases ht : table.lookup input with
  | some output => simp [Program.run, oracle, ht, PMF.pure_map]
  | none =>
      simp only [Program.run, oracle, ht, PMF.bind_map, PMF.map_comp,
        Function.comp_def, List.lookup_cons, beq_self_eq_true,
        PMF.pure_bind, PMF.pure_map]
      rfl

theorem bounded_table {program : Program Input Output Result} {q : Nat}
    (hq : program.BoundedQueries q) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (h : out ∈ (program.run oracle table).support) :
    out.state.length ≤ table.length + q :=
  (run program table out h).2.2.trans
    (Nat.add_le_add_left (hq.trace_length_le oracle table out h) table.length)

/-- Every two public responses to one input agree, even with other adaptive
calls in between and even when different clients make the requests. -/
theorem trace_consistent (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (h : out ∈ (program.run oracle table).support)
    (x : Input) (first second : Output)
    (hf : (x, first) ∈ out.trace) (hs : (x, second) ∈ out.trace) : first = second := by
  have hh := (run program table out h).2.1
  exact Option.some.inj ((hh (x, first) hf).symm.trans (hh (x, second) hs))


/-- A lazy-oracle step adds a chronological prefix and keeps the old table
as a literal suffix. Cached requests add an empty prefix. -/
theorem step_table_extends (table : Table Input Output) (input : Input)
    (answer : Table Input Output × Output)
    (support : answer ∈ (oracle table input).support) :
    ∃ added : Table Input Output, answer.1 = added ++ table := by
  cases ht : table.lookup input with
  | some output =>
      rw [known table input output ht, PMF.mem_support_pure_iff] at support
      subst answer
      exact ⟨[], rfl⟩
  | none =>
      rw [fresh table input ht, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      exact ⟨[(input, output)], rfl⟩

/-- Literal chronological extension holds for arbitrary adaptive executions,
without any uniqueness assumption on the initial table. -/
theorem run_table_extends (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (support : out ∈ (program.run oracle table).support) :
    ∃ added : Table Input Output, out.state = added ++ table := by
  induction program generalizing table out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨[], rfl⟩
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit table out ht
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      obtain ⟨added, he⟩ := step_table_extends table input answer ha
      obtain ⟨later, hl⟩ := ih answer.2 answer.1 tail ht
      exact ⟨later ++ added, by simp only; rw [hl, he, List.append_assoc]⟩

/-- Every stored entry is retained literally, not merely as a lookup answer. -/
theorem step_table_subset (table : Table Input Output) (input : Input)
    (answer : Table Input Output × Output)
    (support : answer ∈ (oracle table input).support) : table ⊆ answer.1 := by
  obtain ⟨added, he⟩ := step_table_extends table input answer support
  rw [he]
  exact fun _ hm => List.mem_append_right _ hm

/-- Every stored edge persists throughout an arbitrary adaptive execution. -/
theorem run_table_subset (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (support : out ∈ (program.run oracle table).support) : table ⊆ out.state := by
  obtain ⟨added, he⟩ := run_table_extends program table out support
  rw [he]
  exact fun _ hm => List.mem_append_right _ hm

/-- Every stored entry agrees with lookup. Unlike public trace consistency,
this excludes shadowed, contradictory entries in an association list. -/
def TableConsistent (table : Table Input Output) : Prop :=
  ∀ entry ∈ table, table.lookup entry.1 = some entry.2

omit [Fintype Output] [Nonempty Output] in
/-- Coherent storage makes the compression graph a function of its input,
even when distinct inputs have colliding outputs. -/
theorem TableConsistent.functional {table : Table Input Output}
    (consistent : TableConsistent table) {input : Input} {left right : Output}
    (hl : (input, left) ∈ table) (hr : (input, right) ∈ table) : left = right :=
  Option.some.inj ((consistent _ hl).symm.trans (consistent _ hr))

omit [Fintype Output] [Nonempty Output] in
/-- Graph functionality suffices for lookup coherence, including lists with
repeated identical entries. No distinct-key representation is required. -/
theorem TableConsistent.of_functional {table : Table Input Output}
    (functional : ∀ input left right, (input, left) ∈ table →
      (input, right) ∈ table → left = right) : TableConsistent table := by
  intro entry hm
  cases he : table.lookup entry.1 with
  | none =>
      have hn := List.lookup_eq_none_iff.mp he entry hm
      simp at hn
  | some value =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      have hv : (entry.1, value) ∈ table := by rw [hs]; simp
      have same := functional entry.1 entry.2 value (by simpa using hm) hv
      rw [same]

omit [Fintype Output] [Nonempty Output] in
/-- Restricting a coherent graph to any sublist preserves coherence, regardless
of public exposure order. -/
theorem TableConsistent.subset {before after : Table Input Output}
    (consistent : TableConsistent after) (includes : before ⊆ after) : TableConsistent before := by
  apply TableConsistent.of_functional
  intro input left right hl hr
  exact consistent.functional (includes hl) (includes hr)

omit [Fintype Output] [Nonempty Output] in
/-- Inserting a fresh input preserves coherent storage for any value. -/
theorem TableConsistent.cons {table : Table Input Output}
    (consistent : TableConsistent table) (input : Input) (output : Output)
    (fresh : table.lookup input = none) : TableConsistent ((input, output) :: table) := by
  intro entry hm
  rcases List.mem_cons.mp hm with rfl | hm
  · simp
  · have old := consistent entry hm
    have different : entry.1 ≠ input := by
      intro he
      rw [he, fresh] at old
      cases old
    simp [List.lookup_cons, beq_eq_false_iff_ne.mpr different, old]

/-- Actual lazy sampling never introduces contradictory stored values. -/
theorem step_table_consistent (table : Table Input Output) (consistent : TableConsistent table)
    (input : Input) (answer : Table Input Output × Output)
    (support : answer ∈ (oracle table input).support) : TableConsistent answer.1 := by
  obtain ⟨records, keeps, _⟩ := step table input answer support
  intro entry hm
  rcases List.mem_cons.mp (step_entries table input answer support hm) with rfl | hm
  · exact records
  · exact keeps entry.1 entry.2 (consistent entry hm)

/-- Stored-table coherence is preserved through arbitrary adaptive interaction,
including local coins. This requires coherence of the supplied initial table. -/
theorem run_table_consistent (program : Program Input Output Result)
    (table : Table Input Output) (consistent : TableConsistent table)
    (out : Outcome Input Output Result (Table Input Output))
    (support : out ∈ (program.run oracle table).support) : TableConsistent out.state := by
  induction program generalizing table out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact consistent
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit table consistent out ht
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact ih answer.2 answer.1 (step_table_consistent table consistent input answer ha) tail ht

/-- The empty-start oracle is functional on all stored entries. No collision
freedom, finite input alphabet, or query bound is assumed. -/
theorem run_empty_table_consistent (program : Program Input Output Result)
    (out : Outcome Input Output Result (Table Input Output))
    (support : out ∈ (program.run oracle []).support) : TableConsistent out.state :=
  run_table_consistent program [] (by intro entry hm; cases hm) out support

end CryptoOracle.RandomOracle
