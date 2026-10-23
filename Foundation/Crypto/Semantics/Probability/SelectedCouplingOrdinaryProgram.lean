import Foundation.Crypto.Semantics.Probability.SelectedCouplingSearch
import Foundation.Crypto.Semantics.Oracle.Program

/-! An ordinary one-coin program realizes every feasible selected binary
coupling graph. This closes an expressivity comparison for the CURRENT mask
fragment; it is not a proof-size or checking-time lower bound. Deterministic
output functions are host terms, just as in the original semantic model. -/
namespace Foundation.Probability.SelectedCouplingGraph.OrdinaryProgram
open CryptoOracle
open Graph
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} (G : Graph Vertex Edge)

/-- One ordinary fair coin followed by a deterministic vector-valued return. -/
def sampler (potential : Vertex → Bool) : Program Unit Unit (Vertex → Bool) :=
  .coin fun bit => .done fun vertex => Bool.xor (potential vertex) bit

noncomputable def law (potential : Vertex → Bool) : PMF (Vertex → Bool) :=
  ((sampler potential).run (fun (_ : Unit) (_ : Unit) => PMF.pure ((), ())) ()).map Outcome.result

theorem sampler_no_queries (potential : Vertex → Bool) : (sampler potential).BoundedQueries 0 :=
  .coin _ _ (fun bit => .done (fun vertex => Bool.xor (potential vertex) bit) 0)

theorem law_eq (potential : Vertex → Bool) : law potential = G.joint potential := by
  simp only [law, sampler, Program.run, PMF.map_bind, PMF.pure_map, sampleBit, Graph.joint]
  rfl

theorem realizes (potential : Vertex → Bool) : G.Realizes (G.boundary potential) (law potential) := by
  rw [law_eq G]
  exact ⟨G.joint_vertex potential, G.joint_edge potential⟩

/-- Arbitrary candidate joint laws add no existence power over the ordinary
one-coin constructor for this selected identity/complement fragment. -/
theorem expressivity_iff (labels : Edge → Bool) :
    (∃ candidate, G.Realizes labels candidate) ↔
    (∃ potential, G.Realizes labels (law potential)) := by
  constructor
  · intro joint
    obtain ⟨potential, rfl⟩ := (G.selected_joint_iff labels).mp joint
    exact ⟨potential, realizes G potential⟩
  · rintro ⟨potential, valid⟩
    exact ⟨law potential, valid⟩

/-- The ordinary program also witnesses the SAME exact feasible repair cost. -/
theorem repair_cost_iff [Fintype Edge] (weight : Edge → Nat) (original : Vertex → Bool)
    (locked : Edge) (cost : Nat) :
    (∃ updated, ∃ candidate, G.Realizes updated candidate ∧
      updated locked ≠ G.boundary original locked ∧ repairCost weight (G.boundary original) updated = cost) ↔
    (∃ potential, G.Realizes (G.boundary potential) (law potential) ∧
      G.boundary potential locked ≠ G.boundary original locked ∧
      repairCost weight (G.boundary original) (G.boundary potential) = cost) := by
  constructor
  · rintro ⟨updated, candidate, valid, changed, price⟩
    obtain ⟨potential, rfl⟩ := (G.selected_joint_iff updated).mp ⟨candidate, valid⟩
    exact ⟨potential, realizes G potential, changed, price⟩
  · rintro ⟨potential, valid, changed, price⟩
    exact ⟨G.boundary potential, law potential, valid, changed, price⟩

variable [DecidableEq Vertex] [Fintype Edge]

/-- The already verified optimal search compiles directly to this ordinary
program, retaining both optimality and the selected edge laws. -/
theorem searched_repair (vertices : List Vertex) (covers : ∀ vertex, vertex ∈ vertices)
    (weight : Edge → Nat) (original : Vertex → Bool) (locked : Edge)
    (certificate : Certificate.Repair Vertex)
    (solved : Search.solve G vertices weight locked = some certificate) :
    G.Realizes (Certificate.repaired G original certificate) (law (shifted original certificate.cut)) ∧
    (sampler (shifted original certificate.cut)).BoundedQueries 0 ∧
    ∀ updated, G.Feasible (G.boundary original) locked updated →
      repairCost weight (G.boundary original) (Certificate.repaired G original certificate) ≤
        repairCost weight (G.boundary original) updated := by
  exact ⟨realizes G _, sampler_no_queries _, Search.solve_optimal G vertices covers weight locked original certificate solved⟩

end Foundation.Probability.SelectedCouplingGraph.OrdinaryProgram
