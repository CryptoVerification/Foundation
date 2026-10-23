import Foundation.Examples.SelectedCouplingRepair
import Foundation.Crypto.Semantics.Probability.SelectedCouplingCertificate

/-! A generated minimum repair certificate for the fan of n triangles.
All definitions are executable; n is not fixed by the soundness theorem. -/
namespace Foundation.Probability.SelectedCouplingGraph.Fan.Checked
open Graph
set_option backward.isDefEq.respectTransparency false

def original {n : Nat} : Fan.Vertex n → Bool := fun _ => false

def certificate (n : Nat) : Certificate.Repair (Fan.Vertex n) := ⟨Fan.potential⟩

theorem shifted_original (n : Nat) : shifted (original (n := n)) Fan.potential = Fan.potential := by
  funext vertex
  simp only [shifted, original]
  cases Fan.potential vertex <;> rfl

theorem generated_labels (n : Nat) :
    Certificate.repaired (Fan.graph n) original (certificate n) = Fan.repair := by
  unfold Certificate.repaired certificate
  rw [shifted_original, ← Fan.repaired_boundary]

theorem cut_cost (n : Nat) : (Fan.graph n).cutCost Fan.weight (certificate n).cut = n := by
  have price := (Fan.graph n).shifted_cost Fan.weight original Fan.potential
  rw [shifted_original, ← Fan.repaired_boundary] at price
  change Graph.repairCost Fan.weight ((Fan.graph n).boundary (fun _ => false)) Fan.repair = _ at price
  rw [← Fan.initial_boundary, Fan.repair_cost] at price
  exact price.symm

theorem accepts (n : Nat) :
    Certificate.validates (Fan.graph n) Fan.weight none n (certificate n) = true := by
  apply (Certificate.validates_iff _ _ _ _ _).mpr
  exact ⟨by change false ≠ true; decide, le_of_eq (cut_cost n)⟩

/-- A zero cut cannot implement the requested change, regardless of budget. -/
theorem rejects_unchanged (n budget : Nat) :
    Certificate.validates (Fan.graph n) Fan.weight none budget ⟨fun _ => false⟩ = false := by
  simp [Certificate.validates, Fan.graph]

/-- The generated certificate meets the exact lower bound on additional edits. -/
theorem minimum (n : Nat) :
    Graph.repairCost Fan.weight Fan.initial
      (Certificate.repaired (Fan.graph n) original (certificate n)) = n ∧
    ∀ (other : Certificate.Repair (Fan.Vertex n)) (budget : Nat),
      Certificate.validates (Fan.graph n) Fan.weight none budget other = true →
      n ≤ Graph.repairCost Fan.weight Fan.initial (Certificate.repaired (Fan.graph n) original other) := by
  refine ⟨?_, ?_⟩
  · rw [generated_labels, Fan.repair_cost]
  · intro other budget accepted
    obtain ⟨joint, changed, _⟩ := Certificate.sound (Fan.graph n) 7 original Fan.weight none budget other accepted
    apply Fan.repair_lower_bound n _
      ((tag_selected_joint_iff (Fan.graph n) 7 _).mp joint)
    have originalFalse : (Fan.graph n).boundary original none = false := rfl
    rw [originalFalse] at changed
    exact Bool.eq_true_of_not_eq_false changed

theorem concrete_accepts :
    Certificate.validates (Fan.graph 3) Fan.weight none 3 (certificate 3) = true := by decide_cbv

theorem concrete_rejects_budget :
    Certificate.validates (Fan.graph 3) Fan.weight none 2 (certificate 3) = false := by decide_cbv

end Foundation.Probability.SelectedCouplingGraph.Fan.Checked
