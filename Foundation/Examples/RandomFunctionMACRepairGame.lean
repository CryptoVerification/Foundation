import Foundation.Examples.RandomFunctionMACCouplingRepair
import Foundation.Examples.SelectedCouplingRepairCertificate

/-! Push selected correspondence repairs through the final verification of the
same adaptive MAC. Every vertex retains the full final cache, verification bit,
and ordered transcript. The original sampled function is retained separately
in the common joint, as in RandomFunctionMACCouplingRepair. -/
namespace Foundation.Symmetric.RandomFunctionMACRepairGame
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACPosterior RandomFunctionMACCouplingRepair
set_option backward.isDefEq.respectTransparency false

abbrev GameOutcome := Outcome (Fin 8) (Fin 256) Bool (Table (Fin 8) (Fin 256))

def finishTag (past : SigningOutcome) (tag : Fin 256) : GameOutcome :=
  ⟨decide (tag = past.result.2), (7, tag) :: past.state, past.trace ++ [(7, tag)]⟩

def finish (past : SigningOutcome) (tag : Bits 8) : GameOutcome :=
  finishTag past (RandomFunctionMACNativeCaller.decodeTag tag.toList)

theorem target_decomposition :
    RandomFunctionMACSchedules.Examples.attack.bind (fun forgery =>
      .query 7 fun actual => .done (decide (actual = forgery.2))) =
      RandomFunctionMACNativeCaller.target := rfl

theorem reference_game_law :
    (signingHistory.bind fun past => (uniform (Bits 8)).map (finish past)) =
      RandomFunctionMACNativeCaller.target.run oracle [] := by
  rw [← target_decomposition, Program.run_bind]
  apply bind_congr_of_support
  intro past supported
  rw [Program.run, fresh past.state 7 (signing_fresh past supported)]
  simp only [PMF.bind_map, Program.run, PMF.pure_map, Function.comp_def]
  have coded := congrArg (fun p => p.map (finishTag past))
    RandomFunctionMACNativeCaller.Backend.uniform_decoded
  simpa only [finish, finishTag, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using coded

variable {Vertex Edge : Type} (G : Graph Vertex Edge)

noncomputable def games (potential : SigningOutcome → Vertex → Bool) :
    PMF (RetainedHistory × (Vertex → GameOutcome)) :=
  (actualJoint potential).map fun pair =>
    (pair.1, fun vertex => finish pair.1.1 (pair.2 vertex))

/-- This marginal includes the actual initial function, not a resampled copy. -/
theorem games_original (potential : SigningOutcome → Vertex → Bool) :
    (games potential).map Prod.fst = CryptoOracle.RandomOracle.Posterior.retained signingHistory Outcome.state := by
  simpa only [games, PMF.map_comp, Function.comp_def] using actual_joint_original potential

include G in
/-- Each vertex is the complete original typed game, including the updated
verification cache and every signing/verification request and response. -/
theorem vertex_game_law (potential : SigningOutcome → Vertex → Bool) (vertex : Vertex) :
    (games potential).map (fun pair => pair.2 vertex) =
      RandomFunctionMACNativeCaller.target.run oracle [] := by
  have vertexLaw := context_joint_vertex G 8 signingHistory potential vertex
  rw [← actual_joint_projection G potential, PMF.map_comp] at vertexLaw
  have law := congrArg (fun p => p.map (fun pair => finish pair.1 pair.2)) vertexLaw
  simp only [games, PMF.map_comp, PMF.map_bind, Function.comp_def] at law ⊢
  exact law.trans reference_game_law

/-- The selected edge law is transported through verification in the SAME
joint as the vertex game laws; it is not chosen independently afterwards. -/
theorem edge_game_law (potential : SigningOutcome → Vertex → Bool)
    (labels : SigningOutcome → Edge → Bool)
    (valid : ∀ past ∈ signingHistory.support, labels past = G.boundary (potential past)) (edge : Edge) :
    (games potential).map (fun pair =>
      (pair.1.1, (pair.2 (G.source edge), pair.2 (G.target edge)))) =
    (contextEdge 8 signingHistory labels edge).map
      (fun pair => (pair.1, (finish pair.1 pair.2.1, finish pair.1 pair.2.2))) := by
  have edgeLaw := context_joint_edge G 8 signingHistory potential labels valid edge
  rw [← actual_joint_projection G potential, PMF.map_comp] at edgeLaw
  have law := congrArg (fun p => p.map (fun pair =>
    (pair.1, (finish pair.1 pair.2.1, finish pair.1 pair.2.2)))) edgeLaw
  simpa only [games, PMF.map_comp, Function.comp_def] using law

include G in
/-- Any postprocessing of the full output is allowed, including probabilistic
ones. This does not add elapsed time to the observation. -/
theorem vertex_continuation {Result : Type} (potential : SigningOutcome → Vertex → Bool)
    (vertex : Vertex) (next : GameOutcome → PMF Result) :
    ((games potential).map (fun pair => pair.2 vertex)).bind next =
      (RandomFunctionMACNativeCaller.target.run oracle []).bind next := by
  rw [vertex_game_law G]

/-- A checked, history-dependent cut computes a repair whose selected edge
laws have a common joint; all its vertex games equal the original full game. -/
theorem checked_repair [Fintype Edge] (original : SigningOutcome → Vertex → Bool)
    (weight : SigningOutcome → Edge → Nat) (locked : SigningOutcome → Edge)
    (budget : SigningOutcome → Nat) (certificate : SigningOutcome → Certificate.Repair Vertex)
    (accepted : ∀ past ∈ signingHistory.support,
      Certificate.validates G (weight past) (locked past) (budget past) (certificate past) = true) :
    ContextRealizes G 8 signingHistory (fun past => Certificate.repaired G (original past) (certificate past))
      ((actualJoint (fun past => Graph.shifted (original past) (certificate past).cut)).map
        (fun pair => (pair.1.1, pair.2))) ∧
    (∀ past ∈ signingHistory.support,
      Certificate.repaired G (original past) (certificate past) (locked past) ≠
          G.boundary (original past) (locked past) ∧
      Graph.repairCost (weight past) (G.boundary (original past))
        (Certificate.repaired G (original past) (certificate past)) ≤ budget past) ∧
    ∀ vertex, (games (fun past => Graph.shifted (original past) (certificate past).cut)).map
      (fun pair => pair.2 vertex) = RandomFunctionMACNativeCaller.target.run oracle [] := by
  refine ⟨actual_joint_realizes G _ _ (fun _ _ => rfl), ?_, vertex_game_law G _⟩
  intro past supported
  exact (Certificate.sound G 7 (original past) (weight past) (locked past) (budget past)
    (certificate past) (accepted past supported)).2

/-- The closed generator for the fan family supplies a checked optimal
certificate for every history of the same MAC. -/
theorem fan_generated (n : Nat) :
    (∀ past ∈ signingHistory.support,
      Certificate.validates (Fan.graph n) Fan.weight none n (Fan.Checked.certificate n) = true) ∧
    (∀ vertex, (games (fun _ => Graph.shifted (Fan.Checked.original (n := n))
        (Fan.Checked.certificate n).cut)).map (fun pair => pair.2 vertex) =
      RandomFunctionMACNativeCaller.target.run oracle []) ∧
    Graph.repairCost Fan.weight Fan.initial
      (Certificate.repaired (Fan.graph n) Fan.Checked.original (Fan.Checked.certificate n)) = n := by
  exact ⟨fun _ _ => Fan.Checked.accepts n,
    vertex_game_law (Fan.graph n) _, (Fan.Checked.minimum n).1⟩

end Foundation.Symmetric.RandomFunctionMACRepairGame
