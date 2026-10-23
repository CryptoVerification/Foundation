import Foundation.Crypto.Semantics.Probability.SelectedCouplingRepair
import Mathlib.Algebra.BigOperators.Fin

/-! An unbounded family of proof graphs. Editing one selected coupling
forces exactly n additional witness edits, although every edge remains a
valid coupling of the unchanged uniform games. Ordinary shared lemmas prove
the same optimum: this is a maintenance lower bound, not a polygraph advantage. -/
namespace Foundation.Probability.SelectedCouplingGraph.Fan
open Graph
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev Vertex (n : Nat) := Fin n ⊕ Bool
abbrev Edge (n : Nat) := Option (Fin n × Bool)

def graph (n : Nat) : Graph (Vertex n) (Edge n) where
  source := fun edge => match edge with
    | none => .inr false
    | some (_index, false) => .inr false
    | some (index, true) => .inl index
  target := fun edge => match edge with
    | none => .inr true
    | some (index, false) => .inl index
    | some (_, true) => .inr true

/-- Root-to-tip edge is the already requested change; the other witnesses
are charged one unit each. -/
def weight {n : Nat} : Edge n → Nat
  | none => 0
  | some _ => 1

def initial {n : Nat} : Edge n → Bool := fun _ => false

def repair {n : Nat} : Edge n → Bool
  | none => true
  | some (_, side) => side

def potential {n : Nat} : Vertex n → Bool
  | .inl _ => false
  | .inr side => side

theorem initial_boundary (n : Nat) : initial (n := n) = (graph n).boundary (fun _ => false) := by
  funext edge
  rfl

theorem repaired_boundary (n : Nat) : repair (n := n) = (graph n).boundary potential := by
  funext edge
  cases edge with
  | none => rfl
  | some edge => obtain ⟨index, side⟩ := edge; cases side <;> rfl

/-- The n triangles form a complete finite set of compatibility tests for
this family. No list of proof paths is an input. -/
theorem coherent_iff_faces (n : Nat) (labels : Edge n → Bool) :
    (graph n).Coherent labels ↔ ∀ index, labels none = Bool.xor (labels (some (index, false))) (labels (some (index, true))) := by
  constructor
  · rintro ⟨values, rfl⟩ index
    simp only [boundary, graph]
    cases values (.inr false) <;> cases values (.inr true) <;> cases values (.inl index) <;> rfl
  · intro faces
    let values : Vertex n → Bool := fun vertex => match vertex with
      | .inl index => labels (some (index, false))
      | .inr false => false
      | .inr true => labels none
    refine ⟨values, ?_⟩
    funext edge
    cases edge with
    | none => simp [boundary, graph, values]
    | some edge =>
        obtain ⟨index, side⟩ := edge
        cases side with
        | false => simp [boundary, graph, values]
        | true =>
            have face := faces index
            simp only [boundary, graph, values]
            cases left : labels (some (index, false)) <;> cases right : labels (some (index, true)) <;>
              cases direct : labels none <;> simp_all

theorem cost_formula (n : Nat) (labels : Edge n → Bool) :
    repairCost weight initial labels =
      ∑ index : Fin n, ((if labels (some (index, false)) then 1 else 0) +
        (if labels (some (index, true)) then 1 else 0)) := by
  unfold repairCost
  rw [Fintype.sum_option]
  simp only [weight, ite_self, Nat.zero_add]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro index _
  rw [Fintype.sum_bool]
  cases labels (some (index, false)) <;> cases labels (some (index, true)) <;> rfl

/-- Editing the direct witness forces at least one edit in every disjoint
branch. This counts changed correspondences, not proof lines or advantage. -/
theorem repair_lower_bound (n : Nat) (labels : Edge n → Bool)
    (coherent : (graph n).Coherent labels) (locked : labels none = true) :
    n ≤ repairCost weight initial labels := by
  rw [cost_formula]
  have faces := (coherent_iff_faces n labels).mp coherent
  have each (index : Fin n) : 1 ≤ (if labels (some (index, false)) then 1 else 0) +
      (if labels (some (index, true)) then 1 else 0) := by
    have face := faces index
    rw [locked] at face
    cases left : labels (some (index, false)) <;> cases right : labels (some (index, true)) <;>
      simp only [left, right] at face ⊢
    all_goals first | contradiction | decide
  calc
    n = ∑ _index : Fin n, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun index _ => each index)

theorem repair_cost (n : Nat) : repairCost weight initial (repair (n := n)) = n := by
  rw [cost_formula]
  simp [repair]

/-- The explicit repair attains the lower bound and all selected pair laws
have a common joint law. The number n is arbitrary. -/
theorem minimum_selected_joint_repair (n : Nat) :
    (∃ candidate : PMF (Vertex n → Bool), (graph n).Realizes repair candidate) ∧
    repairCost weight initial (repair (n := n)) = n ∧
    ∀ labels : Edge n → Bool, labels none = true →
      (∃ candidate : PMF (Vertex n → Bool), (graph n).Realizes labels candidate) →
      n ≤ repairCost weight initial labels := by
  refine ⟨(graph n).selected_joint_iff repair |>.mpr ⟨potential, repaired_boundary n⟩, repair_cost n, ?_⟩
  intro labels locked joint
  exact repair_lower_bound n labels ((graph n).selected_joint_iff labels |>.mp joint) locked

/-- The un-repaired single-edge edit already preserves every endpoint
marginal, but fails simultaneous realization whenever a branch exists. -/
def editedOnly {n : Nat} : Edge n → Bool
  | none => true
  | some _ => false

theorem editedOnly_no_joint (n : Nat) (positive : 0 < n) :
    ¬∃ candidate : PMF (Vertex n → Bool), (graph n).Realizes editedOnly candidate := by
  intro candidate
  have faces := (coherent_iff_faces n editedOnly).mp ((graph n).selected_joint_iff editedOnly |>.mp candidate)
  have impossible := faces ⟨0, positive⟩
  contradiction

theorem editedOnly_marginals (n : Nat) (edge : Edge n) :
    (edgeLaw (editedOnly edge)).map Prod.fst = uniform Bool ∧
      (edgeLaw (editedOnly edge)).map Prod.snd = uniform Bool :=
  ⟨edge_first _, edge_second _⟩

end Foundation.Probability.SelectedCouplingGraph.Fan
