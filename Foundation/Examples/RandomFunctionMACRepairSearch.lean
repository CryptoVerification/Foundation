import Foundation.Crypto.Semantics.Probability.SelectedCouplingSearch
import Foundation.Examples.RandomFunctionMACRepresentationRepair

/-! Automatic optimal repair of the represented-cache MAC games. Weights and
the edge requested for change may depend on the actual signing history. The
finite exhaustive search is shared by the ordinary semantic baseline. -/
namespace Foundation.Symmetric.RandomFunctionMACRepairSearch
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACPosterior RandomFunctionMACRepresentationGame
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} [DecidableEq Vertex] [Fintype Edge]
variable (G : Graph Vertex Edge) (vertices : List Vertex)

/-- On failure retain the old representation; failure is exactly a loop
request when the supplied list covers all vertices. -/
def selectedPotential (original : SigningOutcome → Vertex → Bool)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge) :
    SigningOutcome → Vertex → Bool := fun past =>
  match Search.solve G vertices (weight past) (locked past) with
  | none => original past
  | some certificate => Graph.shifted (original past) certificate.cut

/-- No manual cut is supplied. Every non-loop request gets an optimal
repair, compared against ALL compatible selected edge laws. -/
theorem optimal_at_history (covers : ∀ vertex, vertex ∈ vertices)
    (original : SigningOutcome → Vertex → Bool) (weight : SigningOutcome → Edge → Nat)
    (locked : SigningOutcome → Edge) (past : SigningOutcome)
    (distinct : G.source (locked past) ≠ G.target (locked past)) :
    ∃ certificate,
      Search.solve G vertices (weight past) (locked past) = some certificate ∧
      Certificate.validates G (weight past) (locked past) (G.cutCost (weight past) certificate.cut) certificate = true ∧
      G.boundary (selectedPotential G vertices original weight locked past) (locked past) ≠
        G.boundary (original past) (locked past) ∧
      ∀ updated, G.Feasible (G.boundary (original past)) (locked past) updated →
        Graph.repairCost (weight past) (G.boundary (original past))
          (G.boundary (selectedPotential G vertices original weight locked past)) ≤
          Graph.repairCost (weight past) (G.boundary (original past)) updated := by
  cases solved : Search.solve G vertices (weight past) (locked past) with
  | none => exact False.elim (distinct ((Search.solve_none_iff G vertices covers _ _).mp solved))
  | some certificate =>
      have accepted := Search.solve_accepted G vertices (weight past) (locked past) certificate solved
      refine ⟨certificate, rfl, accepted, ?_, ?_⟩
      · have changed := (Certificate.sound G 7 (original past) (weight past) (locked past)
          (G.cutCost (weight past) certificate.cut) certificate accepted).2.1
        simpa only [selectedPotential, solved, Certificate.repaired] using changed
      · intro updated feasible
        have minimal := Search.solve_optimal G vertices covers (weight past) (locked past)
          (original past) certificate solved updated feasible
        simpa only [selectedPotential, solved, Certificate.repaired] using minimal

/-- The same computed repair determines each operational cache game. -/
theorem operational_vertices (original : SigningOutcome → Vertex → Bool)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge) (vertex : Vertex) :
    (joint (selectedPotential G vertices original weight locked)).map (fun pair => (pair.1.1, pair.2 vertex)) =
      storedGame (fun past => selectedPotential G vertices original weight locked past vertex) :=
  joint_vertex G _ vertex

/-- Its full decoded output, not just the verification probability, is safe
under all branches of the actual adaptive signing history. -/
theorem decoded_vertices (original : SigningOutcome → Vertex → Bool)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge) (vertex : Vertex) :
    (joint (selectedPotential G vertices original weight locked)).map (fun pair =>
      decode (selectedPotential G vertices original weight locked pair.1.1 vertex) (pair.2 vertex)) =
      RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] :=
  decoded_vertex G _ vertex

/-- The optimality statement concerns the edge laws read from the SAME
operational joint of repaired game outputs. -/
theorem operational_edges (original : SigningOutcome → Vertex → Bool)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge) (edge : Edge) :
    (joint (selectedPotential G vertices original weight locked)).map (fun pair => (pair.1.1,
      (storedAnswer (pair.2 (G.source edge)), storedAnswer (pair.2 (G.target edge))))) =
      contextEdge 8 signingHistory
        (fun past => G.boundary (selectedPotential G vertices original weight locked past)) edge :=
  derived_edge_law G _ edge

end Foundation.Symmetric.RandomFunctionMACRepairSearch
