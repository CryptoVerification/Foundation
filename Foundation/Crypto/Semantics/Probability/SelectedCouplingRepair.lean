import Foundation.Crypto.Semantics.Probability.SelectedCouplingGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact correspondence between repairing selected binary coupling graphs
and separating cuts. Cost counts changed witness edges, with arbitrary natural
weights, not probability loss, proof bytes, or machine execution time. -/
namespace Foundation.Probability.SelectedCouplingGraph.Graph
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} (G : Graph Vertex Edge)

def shift (original updated : Vertex → Bool) : Vertex → Bool :=
  fun vertex => Bool.xor (original vertex) (updated vertex)

def shifted (original cut : Vertex → Bool) : Vertex → Bool :=
  fun vertex => Bool.xor (original vertex) (cut vertex)

theorem shifted_shift (original updated : Vertex → Bool) : shifted original (shift original updated) = updated := by
  funext vertex
  simp only [shifted, shift]
  cases original vertex <;> cases updated vertex <;> rfl

theorem boundary_shift (original cut : Vertex → Bool) (edge : Edge) :
    G.boundary (shifted original cut) edge = Bool.xor (G.boundary original edge) (G.boundary cut edge) := by
  simp only [boundary, shifted]
  cases original (G.source edge) <;> cases original (G.target edge) <;>
    cases cut (G.source edge) <;> cases cut (G.target edge) <;> rfl

theorem changed_iff_cut (original updated : Vertex → Bool) (edge : Edge) :
    G.boundary updated edge ≠ G.boundary original edge ↔
      shift original updated (G.source edge) ≠ shift original updated (G.target edge) := by
  simp only [boundary, shift]
  cases original (G.source edge) <;> cases original (G.target edge) <;>
    cases updated (G.source edge) <;> cases updated (G.target edge) <;> decide

theorem shifted_changed_iff (original cut : Vertex → Bool) (edge : Edge) :
    G.boundary (shifted original cut) edge ≠ G.boundary original edge ↔ cut (G.source edge) ≠ cut (G.target edge) := by
  simp only [boundary, shifted]
  cases original (G.source edge) <;> cases original (G.target edge) <;>
    cases cut (G.source edge) <;> cases cut (G.target edge) <;> decide

variable [Fintype Edge]

def repairCost (weight : Edge → Nat) (original updated : Edge → Bool) : Nat :=
  ∑ edge, if updated edge ≠ original edge then weight edge else 0

def cutCost (weight : Edge → Nat) (cut : Vertex → Bool) : Nat :=
  ∑ edge, if cut (G.source edge) ≠ cut (G.target edge) then weight edge else 0

theorem boundary_cost (weight : Edge → Nat) (original updated : Vertex → Bool) :
    repairCost weight (G.boundary original) (G.boundary updated) = G.cutCost weight (shift original updated) := by
  apply Finset.sum_congr rfl
  intro edge _
  simp only [G.changed_iff_cut]

theorem shifted_cost (weight : Edge → Nat) (original cut : Vertex → Bool) :
    repairCost weight (G.boundary original) (G.boundary (shifted original cut)) = G.cutCost weight cut := by
  apply Finset.sum_congr rfl
  intro edge _
  simp only [G.shifted_changed_iff]

def Feasible (original : Edge → Bool) (locked : Edge) (updated : Edge → Bool) : Prop :=
  G.Coherent updated ∧ updated locked ≠ original locked

/-- ALL feasible repaired graphs correspond to separating cuts with exactly
matching costs. The initially selected witnesses are coherent by construction. -/
theorem feasible_cost_iff (weight : Edge → Nat) (original : Vertex → Bool) (locked : Edge) (cost : Nat) :
    (∃ updated, G.Feasible (G.boundary original) locked updated ∧
      repairCost weight (G.boundary original) updated = cost) ↔
    (∃ cut : Vertex → Bool, cut (G.source locked) ≠ cut (G.target locked) ∧ G.cutCost weight cut = cost) := by
  constructor
  · rintro ⟨updated, ⟨⟨potential, rfl⟩, changed⟩, costEq⟩
    exact ⟨shift original potential, (G.changed_iff_cut original potential locked).mp changed,
      (G.boundary_cost weight original potential).symm.trans costEq⟩
  · rintro ⟨cut, separated, costEq⟩
    exact ⟨G.boundary (shifted original cut),
      ⟨⟨shifted original cut, rfl⟩, (G.shifted_changed_iff original cut locked).mpr separated⟩,
      (G.shifted_cost weight original cut).trans costEq⟩

/-- The cut characterization applies to exact simultaneous realizations
of the selected pairwise probability laws, not only to syntactic labels. -/
theorem selected_joint_repair_cost_iff (weight : Edge → Nat) (original : Vertex → Bool)
    (locked : Edge) (cost : Nat) :
    (∃ updated, ∃ candidate : PMF (Vertex → Bool), G.Realizes updated candidate ∧
      updated locked ≠ G.boundary original locked ∧ repairCost weight (G.boundary original) updated = cost) ↔
    (∃ cut : Vertex → Bool, cut (G.source locked) ≠ cut (G.target locked) ∧ G.cutCost weight cut = cost) := by
  rw [← G.feasible_cost_iff weight original locked cost]
  constructor
  · rintro ⟨updated, candidate, realizes, changed, price⟩
    exact ⟨updated, ⟨(G.selected_joint_iff updated).mp ⟨candidate, realizes⟩, changed⟩, price⟩
  · rintro ⟨updated, ⟨coherent, changed⟩, price⟩
    obtain ⟨candidate, realizes⟩ := (G.selected_joint_iff updated).mpr coherent
    exact ⟨updated, candidate, realizes, changed, price⟩

/-- A chosen repair is globally minimum exactly when its cut is a minimum
separating cut. This characterizes the optimization problem; it does not
claim a verified polynomial-time min-cut implementation. -/
theorem minimum_repair_iff (weight : Edge → Nat) (original : Vertex → Bool) (locked : Edge)
    (cut : Vertex → Bool) (_separated : cut (G.source locked) ≠ cut (G.target locked)) :
    (∀ updated, G.Feasible (G.boundary original) locked updated →
      repairCost weight (G.boundary original) (G.boundary (shifted original cut)) ≤
        repairCost weight (G.boundary original) updated) ↔
    (∀ other : Vertex → Bool, other (G.source locked) ≠ other (G.target locked) → G.cutCost weight cut ≤ G.cutCost weight other) := by
  rw [G.shifted_cost]
  constructor
  · intro optimal other separation
    have candidate := optimal (G.boundary (shifted original other))
      ⟨⟨shifted original other, rfl⟩, (G.shifted_changed_iff original other locked).mpr separation⟩
    rwa [G.shifted_cost] at candidate
  · intro optimal updated feasible
    obtain ⟨other, separated, cost⟩ := (G.feasible_cost_iff weight original locked
      (repairCost weight (G.boundary original) updated)).mp ⟨updated, feasible, rfl⟩
    exact (optimal other separated).trans (le_of_eq cost)

end Foundation.Probability.SelectedCouplingGraph.Graph
