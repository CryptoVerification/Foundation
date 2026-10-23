import Foundation.Crypto.Semantics.Probability.SelectedCouplingCertificate
import Mathlib.Data.List.MinMax

/-! Executable exhaustive optimal repair search for a supplied finite vertex
list. Search enumerates subsets, not proof paths. It is exponential in the
list length; no polynomial-time minimum-cut algorithm is claimed. -/
namespace Foundation.Probability.SelectedCouplingGraph.Search
open Graph
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} [DecidableEq Vertex]

def cuts : List Vertex → List (Vertex → Bool)
  | [] => [fun _ => false]
  | vertex :: rest => (cuts rest).flatMap fun cut =>
      [Function.update cut vertex false, Function.update cut vertex true]

theorem cuts_length (vertices : List Vertex) : (cuts vertices).length = 2 ^ vertices.length := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
      simp only [cuts, List.length_flatMap, List.length_cons, List.length_nil]
      simp [ih, Nat.pow_succ, Nat.mul_comm]

/-- Enumeration covers every assignment on the supplied vertices, even
when the list has duplicate vertices. -/
theorem cuts_cover (vertices : List Vertex) (assignment : Vertex → Bool) :
    ∃ cut ∈ cuts vertices, ∀ vertex ∈ vertices, cut vertex = assignment vertex := by
  induction vertices with
  | nil => exact ⟨fun _ => false, by simp [cuts], by simp⟩
  | cons vertex rest ih =>
      obtain ⟨cut, member, agrees⟩ := ih
      refine ⟨Function.update cut vertex (assignment vertex), ?_, ?_⟩
      · simp only [cuts, List.mem_flatMap]
        refine ⟨cut, member, ?_⟩
        cases assignment vertex <;> simp
      · intro other included
        by_cases same : other = vertex
        · subst other; simp
        · rw [Function.update_of_ne same]
          exact agrees other ((List.mem_cons.mp included).resolve_left same)

theorem cuts_complete (vertices : List Vertex) (covers : ∀ vertex, vertex ∈ vertices)
    (assignment : Vertex → Bool) : assignment ∈ cuts vertices := by
  obtain ⟨cut, member, agrees⟩ := cuts_cover vertices assignment
  have same : cut = assignment := funext fun vertex => agrees vertex (covers vertex)
  rwa [same] at member

variable (G : Graph Vertex Edge) [Fintype Edge]

def candidates (vertices : List Vertex) (locked : Edge) : List (Vertex → Bool) :=
  (cuts vertices).filter fun cut => cut (G.source locked) ≠ cut (G.target locked)

def solve (vertices : List Vertex) (weight : Edge → Nat) (locked : Edge) : Option (Certificate.Repair Vertex) :=
  ((candidates G vertices locked).argmin (G.cutCost weight)).map Certificate.Repair.mk

theorem solve_spec (vertices : List Vertex) (weight : Edge → Nat) (locked : Edge)
    (certificate : Certificate.Repair Vertex) (solved : solve G vertices weight locked = some certificate) :
    certificate.cut ∈ candidates G vertices locked ∧
    ∀ cut ∈ candidates G vertices locked, G.cutCost weight certificate.cut ≤ G.cutCost weight cut := by
  rw [solve, Option.map_eq_some_iff] at solved
  obtain ⟨cut, selected, same⟩ := solved
  subst certificate
  have member : cut ∈ (candidates G vertices locked).argmin (G.cutCost weight) := by
    rw [selected]; simp
  exact ⟨List.argmin_mem member, fun other included => List.le_of_mem_argmin included member⟩

theorem solve_accepted (vertices : List Vertex) (weight : Edge → Nat) (locked : Edge)
    (certificate : Certificate.Repair Vertex) (solved : solve G vertices weight locked = some certificate) :
    Certificate.validates G weight locked (G.cutCost weight certificate.cut) certificate = true := by
  apply (Certificate.validates_iff G _ _ _ _).mpr
  have member := (solve_spec G vertices weight locked certificate solved).1
  exact ⟨by simpa only [decide_eq_true_eq] using (List.mem_filter.mp member).2, le_rfl⟩

/-- Minimum among all feasible repaired joint laws, not only generated cuts. -/
theorem solve_optimal (vertices : List Vertex) (covers : ∀ vertex, vertex ∈ vertices)
    (weight : Edge → Nat) (locked : Edge) (original : Vertex → Bool)
    (certificate : Certificate.Repair Vertex) (solved : solve G vertices weight locked = some certificate)
    (updated : Edge → Bool) (feasible : G.Feasible (G.boundary original) locked updated) :
    repairCost weight (G.boundary original) (Certificate.repaired G original certificate) ≤
      repairCost weight (G.boundary original) updated := by
  obtain ⟨cut, separated, price⟩ := (G.feasible_cost_iff weight original locked
    (repairCost weight (G.boundary original) updated)).mp ⟨updated, feasible, rfl⟩
  have included : cut ∈ candidates G vertices locked :=
    List.mem_filter.mpr ⟨cuts_complete vertices covers cut, by simpa only [decide_eq_true_eq] using separated⟩
  have bound := (solve_spec G vertices weight locked certificate solved).2 cut included
  exact (G.shifted_cost weight original certificate.cut).trans_le (bound.trans_eq price)

/-- The checked search is budget-complete: it rejects a budget exactly
when no simultaneously realizable repair can fit that budget. -/
theorem solve_budget_complete (width : Nat) (vertices : List Vertex)
    (covers : ∀ vertex, vertex ∈ vertices) (weight : Edge → Nat) (locked : Edge)
    (original : Vertex → Bool) (certificate : Certificate.Repair Vertex)
    (solved : solve G vertices weight locked = some certificate) (budget : Nat) :
    Certificate.validates G weight locked budget certificate = true ↔
    ∃ updated, ∃ candidate, TagRealizes G (width + 1) updated candidate ∧
      updated locked ≠ G.boundary original locked ∧
      repairCost weight (G.boundary original) updated ≤ budget := by
  constructor
  · intro accepted
    obtain ⟨⟨candidate, realizes⟩, changed, bounded⟩ :=
      Certificate.sound G width original weight locked budget certificate accepted
    exact ⟨Certificate.repaired G original certificate, candidate, realizes, changed, bounded⟩
  · rintro ⟨updated, candidate, realizes, changed, bounded⟩
    have optimal := solve_optimal G vertices covers weight locked original certificate solved updated
      ⟨(tag_selected_joint_iff G width updated).mp ⟨candidate, realizes⟩, changed⟩
    rw [Certificate.repaired, G.shifted_cost] at optimal
    have separated := (Certificate.validates_iff G _ _ _ _).mp
      (solve_accepted G vertices weight locked certificate solved)
    exact (Certificate.validates_iff G _ _ _ _).mpr ⟨separated.1, optimal.trans bounded⟩

theorem solve_none_iff (vertices : List Vertex) (covers : ∀ vertex, vertex ∈ vertices)
    (weight : Edge → Nat) (locked : Edge) :
    solve G vertices weight locked = none ↔ G.source locked = G.target locked := by
  simp only [solve, Option.map_eq_none_iff, List.argmin_eq_none]
  constructor
  · intro empty
    by_contra distinct
    let cut : Vertex → Bool := fun vertex => decide (vertex = G.source locked)
    have separated : cut (G.source locked) ≠ cut (G.target locked) := by
      simp [cut, Ne.symm distinct]
    have included : cut ∈ candidates G vertices locked :=
      List.mem_filter.mpr ⟨cuts_complete vertices covers cut, by simpa only [decide_eq_true_eq] using separated⟩
    rw [empty] at included
    contradiction
  · intro same
    simp [candidates, same]

end Foundation.Probability.SelectedCouplingGraph.Search
