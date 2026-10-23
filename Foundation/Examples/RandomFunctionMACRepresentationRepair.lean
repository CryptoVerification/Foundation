import Foundation.Examples.RandomFunctionMACRepresentationGame

/-! Supplied-cut repairs now change actual stored-cache games. The edge
correspondences are the laws of values read from those final caches.
All proofs use the same ordinary operational and probability lemmas. -/
namespace Foundation.Symmetric.RandomFunctionMACRepresentationRepair
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACPosterior RandomFunctionMACRepresentationGame
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} (G : Graph Vertex Edge)

/-- A repair selects new representations at the vertices on the cut. -/
def repairedPotential (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex) : SigningOutcome → Vertex → Bool :=
  fun past => Graph.shifted (original past) (certificate past).cut

theorem derived_changes (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex) (past : SigningOutcome) (edge : Edge) :
    G.boundary (repairedPotential original certificate past) edge ≠ G.boundary (original past) edge ↔
      (certificate past).cut (G.source edge) ≠ (certificate past).cut (G.target edge) :=
  G.shifted_changed_iff (original past) (certificate past).cut edge

/-- The checker budgets changes to the DERIVED stored-value edge laws. -/
theorem checked_changes [Fintype Edge] (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge)
    (budget : SigningOutcome → Nat)
    (accepted : ∀ past ∈ signingHistory.support,
      Certificate.validates G (weight past) (locked past) (budget past) (certificate past) = true) :
    ∀ past ∈ signingHistory.support,
      G.boundary (repairedPotential original certificate past) (locked past) ≠
        G.boundary (original past) (locked past) ∧
      Graph.repairCost (weight past) (G.boundary (original past))
        (G.boundary (repairedPotential original certificate past)) ≤ budget past := by
  intro past supported
  exact (Certificate.sound G 7 (original past) (weight past) (locked past) (budget past)
    (certificate past) (accepted past supported)).2

include G in
/-- The generated repaired joint runs each vertex's actual represented oracle. -/
theorem operational_vertices (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex) (vertex : Vertex) :
    (joint (repairedPotential original certificate)).map (fun pair => (pair.1.1, pair.2 vertex)) =
      storedGame (fun past => repairedPotential original certificate past vertex) :=
  joint_vertex G _ vertex

/-- Selected edge laws are obtained by reading the repaired actual caches. -/
theorem operational_edges (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex) (edge : Edge) :
    (joint (repairedPotential original certificate)).map (fun pair => (pair.1.1,
      (storedAnswer (pair.2 (G.source edge)), storedAnswer (pair.2 (G.target edge))))) =
      contextEdge 8 signingHistory (fun past => G.boundary (repairedPotential original certificate past)) edge :=
  derived_edge_law G _ edge

include G in
/-- Each full game, after decoding its actual cache, remains the original. -/
theorem decoded_vertices (original : SigningOutcome → Vertex → Bool)
    (certificate : SigningOutcome → Certificate.Repair Vertex) (vertex : Vertex) :
    (joint (repairedPotential original certificate)).map (fun pair =>
      decode (repairedPotential original certificate pair.1.1 vertex) (pair.2 vertex)) =
      RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] :=
  decoded_vertex G _ vertex

/-- The closed fan generator changes operational representations and attains
exactly the same minimum edge-change cost as the semantic baseline. -/
theorem fan_generated_cost (n : Nat) :
    (∀ past ∈ signingHistory.support,
      Certificate.validates (Fan.graph n) Fan.weight none n (Fan.Checked.certificate n) = true) ∧
    ∀ past : SigningOutcome,
      Graph.repairCost Fan.weight Fan.initial
        ((Fan.graph n).boundary (repairedPotential (fun _ => Fan.Checked.original)
          (fun _ => Fan.Checked.certificate n) past)) = n := by
  exact ⟨fun _ _ => Fan.Checked.accepts n, fun _ => (Fan.Checked.minimum n).1⟩

end Foundation.Symmetric.RandomFunctionMACRepresentationRepair
