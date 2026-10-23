import Foundation.Crypto.Semantics.Probability.SelectedCouplingSearch
import Foundation.Examples.SelectedCouplingRepair

/-! Computed optimal repairs, including nonuniform weights and impossible
loop requests. The generic fan cost is proved for every n, not extrapolated
from the closed examples. -/
namespace Foundation.Probability.SelectedCouplingGraph.Fan.SearchExample
open Graph
set_option backward.isDefEq.respectTransparency false

def vertices (n : Nat) : List (Fan.Vertex n) :=
  (List.finRange n).map Sum.inl ++ [Sum.inr false, Sum.inr true]

theorem covers (n : Nat) (vertex : Fan.Vertex n) : vertex ∈ vertices n := by
  cases vertex with
  | inl index => simp [vertices]
  | inr side => cases side <;> simp [vertices]

theorem enumeration_size (n : Nat) : (Search.cuts (vertices n)).length = 2 ^ (n + 2) := by
  rw [Search.cuts_length]
  simp [vertices]

theorem selected_cost (n : Nat) (certificate : Certificate.Repair (Fan.Vertex n))
    (solved : Search.solve (Fan.graph n) (vertices n) Fan.weight none = some certificate) :
    (Fan.graph n).cutCost Fan.weight certificate.cut = n := by
  have accepted := Search.solve_accepted (Fan.graph n) (vertices n) Fan.weight none certificate solved
  have sound := Certificate.sound (Fan.graph n) 7 (fun _ => false) Fan.weight none
    ((Fan.graph n).cutCost Fan.weight certificate.cut) certificate accepted
  have coherent := (tag_selected_joint_iff (Fan.graph n) 7 _).mp sound.1
  have changed : Certificate.repaired (Fan.graph n) (fun _ => false) certificate none = true := by
    have difference := sound.2.1
    change Certificate.repaired (Fan.graph n) (fun _ => false) certificate none ≠ false at difference
    exact Bool.eq_true_of_not_eq_false difference
  have lower := Fan.repair_lower_bound n _ coherent changed
  have price : repairCost Fan.weight Fan.initial
      (Certificate.repaired (Fan.graph n) (fun _ => false) certificate) =
      (Fan.graph n).cutCost Fan.weight certificate.cut := by
    simpa only [Certificate.repaired, ← Fan.initial_boundary] using
      (Fan.graph n).shifted_cost Fan.weight (fun _ => false) certificate.cut
  have upper := Search.solve_optimal (Fan.graph n) (vertices n) (covers n) Fan.weight none
    (fun _ => false) certificate solved Fan.repair
    ⟨⟨Fan.potential, Fan.repaired_boundary n⟩, by change true ≠ false; decide⟩
  rw [← Fan.initial_boundary, price, Fan.repair_cost] at upper
  rw [price] at lower
  exact Nat.le_antisymm upper lower

theorem always_finds (n : Nat) :
    ∃ certificate, Search.solve (Fan.graph n) (vertices n) Fan.weight none = some certificate ∧
      (Fan.graph n).cutCost Fan.weight certificate.cut = n := by
  cases solved : Search.solve (Fan.graph n) (vertices n) Fan.weight none with
  | none =>
      have impossible := (Search.solve_none_iff (Fan.graph n) (vertices n) (covers n) Fan.weight none).mp solved
      cases impossible
  | some certificate => exact ⟨certificate, rfl, selected_cost n certificate solved⟩

/-- Ground computation exercises enumeration, filtering, scoring and choice. -/
theorem computed_three :
    (Search.solve (Fan.graph 3) (vertices 3) Fan.weight none).map
      (fun certificate => (Fan.graph 3).cutCost Fan.weight certificate.cut) = some 3 := by decide_cbv

def weighted : Fan.Edge 1 → Nat
  | none => 0
  | some (_, false) => 2
  | some (_, true) => 7

theorem computed_weighted :
    (Search.solve (Fan.graph 1) (vertices 1) weighted none).map
      (fun certificate => (Fan.graph 1).cutCost weighted certificate.cut) = some 2 := by decide_cbv

/-- The old fixed fan repair is feasible but not optimal for these weights. -/
theorem fixed_cut_weighted_cost : (Fan.graph 1).cutCost weighted Fan.potential = 7 := by decide_cbv

def loopGraph : Graph Bool Unit := ⟨fun _ => false, fun _ => false⟩

theorem computed_impossible_loop : Search.solve loopGraph [false, true] (fun _ => 1) () = none := by
  decide_cbv

end Foundation.Probability.SelectedCouplingGraph.Fan.SearchExample
