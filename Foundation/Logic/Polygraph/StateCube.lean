import Foundation.Logic.Polygraph.Rewriting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Insert

/-! Local squares for retained states, rather than equality of output laws.
`State` is a total space with a vertex map: a dependent family `R S` can be
represented by `Σ S, R S`. Thus different vertices need not have the same
payload type. Reapplying an already present change is an administrative no-op.
Only squares involving two fresh, distinct changes are proof obligations. -/
namespace Foundation.Logic.Polygraph

universe u v

/-- Actual state maps together with local, pointwise square certificates. -/
structure StateCube (I : Type u) [DecidableEq I] where
  State : Type v
  vertex : State → Finset I
  step : I → State → State
  vertex_step : ∀ i x, vertex (step i x) = insert i (vertex x)
  step_present : ∀ i x, i ∈ vertex x → step i x = x
  square : ∀ i j x, i ≠ j → i ∉ vertex x → j ∉ vertex x →
    step j (step i x) = step i (step j x)

namespace StateCube

/-- A direct interface for a dependent family of state types. `HEq` compares
payloads whose target types are identified by the corresponding set equality.
Present labels must act as identity, including that type transport. -/
def ofFamily {I : Type u} [DecidableEq I] (R : Finset I → Type v)
    (change : ∀ S i, R S → R (insert i S))
    (idle : ∀ S i x, i ∈ S → HEq (change S i x) x)
    (squares : ∀ S i j x, i ≠ j → i ∉ S → j ∉ S →
      HEq (change (insert i S) j (change S i x))
        (change (insert j S) i (change S j x))) : StateCube I where
  State := Σ S, R S
  vertex := Sigma.fst
  step i x := ⟨insert i x.1, change x.1 i x.2⟩
  vertex_step _ _ := rfl
  step_present _ _ hi := Sigma.ext (Finset.insert_eq_of_mem hi) (idle _ _ _ hi)
  square i j x hij hi hj := Sigma.ext (Finset.insert_comm j i x.1)
    (squares _ _ _ _ hij hi hj)

/-- A convenience constructor for ordinary commuting payload operations.
The applied-set register makes repeated changes administrative identities. -/
def ofCommuting {I : Type u} [DecidableEq I] {A : Type v}
    (change : I → A → A)
    (commuting : ∀ i j x, change j (change i x) = change i (change j x)) : StateCube I where
  State := Finset I × A
  vertex := Prod.fst
  step i x := if i ∈ x.1 then x else (insert i x.1, change i x.2)
  vertex_step i x := by
    by_cases hi : i ∈ x.1 <;> simp [hi, Finset.insert_eq_of_mem]
  step_present i x hi := by simp [hi]
  square i j x hij hi hj := by
    simp only [hi, hj, if_false, Finset.mem_insert, Ne.symm hij, hij, false_or]
    exact Prod.ext (Finset.insert_comm j i x.1) (commuting i j x.2)

variable {I : Type u} [DecidableEq I] (C : StateCube.{u, v} I)

/-- Typed states at a vertex, including heterogeneous retained payloads. -/
abbrev Fiber (S : Finset I) := {x : C.State // C.vertex x = S}

def edge (S : Finset I) (i : I) (x : C.Fiber S) : C.Fiber (insert i S) :=
  ⟨C.step i x.1, by rw [C.vertex_step, x.2]⟩

/-- The fresh squares also give commutation of the saturated operations. -/
theorem commute (i j : I) (x : C.State) :
    C.step j (C.step i x) = C.step i (C.step j x) := by
  by_cases hij : i = j
  · subst j; rfl
  by_cases hi : i ∈ C.vertex x
  · rw [C.step_present i x hi,
      C.step_present i (C.step j x) (by simp [C.vertex_step, hi])]
  by_cases hj : j ∈ C.vertex x
  · rw [C.step_present j x hj,
      C.step_present j (C.step i x) (by simp [C.vertex_step, hj])]
  exact C.square i j x hij hi hj

/-- An executable evaluator for a supplied order; it never enumerates vertices. -/
def run (order : List I) (x : C.State) : C.State :=
  order.foldl (fun state i => C.step i state) x

@[simp] theorem run_nil (x : C.State) : C.run [] x = x := rfl

@[simp] theorem run_cons (i : I) (order : List I) (x : C.State) :
    C.run (i :: order) x = C.run order (C.step i x) := rfl

theorem run_append (a b : List I) (x : C.State) :
    C.run (a ++ b) x = C.run b (C.run a x) := List.foldl_append

/-- Adjacent transpositions suffice; global path independence is a theorem. -/
theorem run_perm {a b : List I} (h : a.Perm b) (x : C.State) :
    C.run a x = C.run b x := by
  induction h generalizing x with
  | nil => rfl
  | cons i h ih => exact ih (C.step i x)
  | swap i j rest => simp only [run_cons]; rw [C.commute]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ x).trans (ih₂ x)

theorem run_step (order : List I) (i : I) (x : C.State) :
    C.run order (C.step i x) = C.step i (C.run order x) := by
  induction order generalizing x with
  | nil => rfl
  | cons j rest ih =>
    simp only [run_cons]
    rw [C.commute i j x, ih]

theorem vertex_run (order : List I) (x : C.State) :
    C.vertex (C.run order x) = C.vertex x ∪ order.toFinset := by
  induction order generalizing x with
  | nil => simp
  | cons i rest ih =>
    simp only [run_cons, ih, C.vertex_step, List.toFinset_cons]
    ext j
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

/-- The four-dimensional generators exchange two adjacent transformations.
The surrounding prefix and suffix are retained as explicit context. -/
inductive Exchange : List I → List I → Type u where
  | adjacent (before after : List I) (i j : I) :
      Exchange (before ++ i :: j :: after) (before ++ j :: i :: after)

abbrev Comparison (a b : List I) := Track (@Exchange I) a b

theorem exchange_sound {a b : List I} (e : Exchange a b) (x : C.State) :
    C.run a x = C.run b x := by
  cases e with
  | adjacent before after i j =>
    simp only [run_append, run_cons]
    rw [C.commute]

theorem comparison_sound {a b : List I} (p : Comparison a b) (x : C.State) :
    C.run a x = C.run b x := by
  induction p with
  | refl => rfl
  | step e => exact C.exchange_sound e x
  | comp p q ih₁ ih₂ => exact ih₁.trans ih₂
  | inv p ih => exact ih.symm

omit [DecidableEq I] in
/-- Every permutation has an explicit comparison built from adjacent squares.
The existential is propositional because `List.Perm` itself is a proposition. -/
theorem comparison_complete {a b : List I} (h : a.Perm b) :
    Nonempty (Comparison a b) := by
  induction h with
  | nil => exact ⟨.refl []⟩
  | cons i h ih =>
    obtain ⟨p⟩ := ih
    exact ⟨p.map (List.cons i) (fun e => by
      cases e with
      | adjacent before after j k =>
        exact .adjacent (i :: before) after j k)⟩
  | swap i j rest => exact ⟨.step (.adjacent [] rest j i)⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p⟩ := ih₁
    obtain ⟨q⟩ := ih₂
    exact ⟨.comp p q⟩

theorem comparison_of_same_changes {a b : List I} (ha : a.Nodup) (hb : b.Nodup)
    (h : a.toFinset = b.toFinset) : Nonempty (Comparison a b) :=
  comparison_complete (List.perm_of_nodup_nodup_toFinset_eq ha hb h)

/-- A mathematical choice of order. For execution use `run` with a supplied
duplicate-free list; `query_order` certifies that implementation. -/
noncomputable def query (x : C.State) (S : Finset I) : C.State := C.run S.toList x

@[simp] theorem query_empty (x : C.State) : C.query x ∅ = x := by simp [query]

theorem query_order (x : C.State) {order : List I} (hn : order.Nodup) :
    C.query x order.toFinset = C.run order x :=
  C.run_perm (List.toFinset_toList hn) x

theorem vertex_query (x : C.State) (S : Finset I) :
    C.vertex (C.query x S) = C.vertex x ∪ S := by
  simp [query, C.vertex_run]

/-- All edges of the cube hold simultaneously for this one root state. -/
theorem query_insert (x : C.State) (S : Finset I) (i : I) :
    C.query x (insert i S) = C.step i (C.query x S) := by
  by_cases hi : i ∈ S
  · rw [Finset.insert_eq_of_mem hi]
    exact (C.step_present i _ (by simp [C.vertex_query, hi])).symm
  · calc
      _ = C.run (S.toList ++ [i]) x := C.run_perm
        ((Finset.toList_insert hi).trans (by
          simpa using (List.perm_append_comm :
            ([i] ++ S.toList).Perm (S.toList ++ [i])))) x
      _ = _ := by simp [run_append, query]

/-- Administrative repetitions do not change the constructed state. -/
theorem run_eq_query (order : List I) (x : C.State) :
    C.run order x = C.query x order.toFinset := by
  induction order generalizing x with
  | nil => simp
  | cons i rest ih =>
    rw [run_cons, ih, List.toFinset_cons, C.query_insert]
    exact C.run_step rest.toFinset.toList i x

theorem run_same_changes {a b : List I} (h : a.toFinset = b.toFinset) (x : C.State) :
    C.run a x = C.run b x := by rw [C.run_eq_query, C.run_eq_query, h]

/-- Edge compatibility determines the entire assignment from its root. -/
theorem assignment_unique (assignment : Finset I → C.State)
    (edges : ∀ S i, assignment (insert i S) = C.step i (assignment S))
    (S : Finset I) : assignment S = C.query (assignment ∅) S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [edges, C.query_insert, ih]

/-- An instrumented evaluator counts one application of `step` per list entry.
This counts transformations, not the machine time of an arbitrary state map. -/
def runCount : List I → C.State → C.State × Nat
  | [], x => (x, 0)
  | i :: rest, x =>
    let result := runCount rest (C.step i x)
    (result.1, result.2 + 1)

theorem runCount_eq (order : List I) (x : C.State) :
    C.runCount order x = (C.run order x, order.length) := by
  induction order generalizing x with
  | nil => rfl
  | cons i rest ih => simp [runCount, ih]

theorem query_transformations (x : C.State) (S : Finset I) :
    (C.runCount S.toList x).2 = S.card := by
  rw [C.runCount_eq, Finset.length_toList]

/-- A separate accounting of the supplied cost of each actual state map. -/
def runCost (cost : I → C.State → Nat) : List I → C.State → C.State × Nat
  | [], x => (x, 0)
  | i :: rest, x =>
    let result := runCost cost rest (C.step i x)
    (result.1, cost i x + result.2)

theorem runCost_state (cost : I → C.State → Nat) (order : List I) (x : C.State) :
    (C.runCost cost order x).1 = C.run order x := by
  induction order generalizing x with
  | nil => rfl
  | cons i rest ih => exact ih (C.step i x)

/-- Uniform local costs imply a linear bound in the number of transformations.
Encoding, copying, and set management must be included by an implementation
before interpreting this accounting as a machine-time bound. -/
theorem runCost_le (cost : I → C.State → Nat) (h : Nat)
    (bound : ∀ i x, cost i x ≤ h) (order : List I) (x : C.State) :
    (C.runCost cost order x).2 ≤ order.length * h := by
  induction order generalizing x with
  | nil => simp [runCost]
  | cons i rest ih =>
    simp only [runCost, List.length_cons]
    calc
      _ ≤ h + rest.length * h := Nat.add_le_add (bound i x) (ih (C.step i x))
      _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem query_cost_le (cost : I → C.State → Nat) (h : Nat)
    (bound : ∀ i x, cost i x ≤ h) (S : Finset I) (x : C.State) :
    (C.runCost cost S.toList x).2 ≤ S.card * h := by
  simpa only [Finset.length_toList] using C.runCost_le cost h bound S.toList x

end StateCube
end Foundation.Logic.Polygraph
