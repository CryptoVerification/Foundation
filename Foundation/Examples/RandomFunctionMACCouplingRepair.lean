import Foundation.Crypto.Semantics.Probability.SelectedCouplingContext
import Foundation.Examples.SelectedCouplingRepair
import Foundation.Examples.RandomFunctionMACPosterior
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeInterface

/-! Selected correspondence repair for the same adaptive 8-message/256-tag
MAC. The original sampled function is retained. These are proof couplings of
future verification answers, not new commands of the adversary or a change in
its success probability. The ordinary proof imports no diagram syntax here. -/
namespace Foundation.Symmetric.RandomFunctionMACCouplingRepair
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
open RandomFunctionMACPosterior
set_option backward.isDefEq.respectTransparency false

abbrev FunctionState := Fin 8 → Fin 256
abbrev RetainedHistory := SigningOutcome × FunctionState

/-- The real unqueried answer, encoded using the existing native interface. -/
theorem actual_answer_law :
    (retained signingHistory Outcome.state).map
      (fun pair => (pair.1, RandomFunctionMACNativeCaller.Backend.tagBits (pair.2 7))) =
      signingHistory.bind (fun past => (uniform (Bits 8)).map fun tag => (past, tag)) := by
  simp only [retained, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_of_support
  intro past supported
  have law := congrArg (fun p => p.map (fun tag => (past, RandomFunctionMACNativeCaller.Backend.tagBits tag)))
    (reserve_fresh past.state 7 (signing_fresh past supported))
  simp only [PMF.map_comp, Function.comp_def] at law
  rw [law]
  have encoded := uniform_map_equiv RandomFunctionMACNativeCaller.Backend.tagEquiv
  have result := congrArg (fun p => p.map (fun tag => (past, tag))) encoded
  simpa only [PMF.map_comp, Function.comp_def, RandomFunctionMACNativeCaller.Backend.tagEquiv,
    Equiv.coe_fn_mk] using result

variable {Vertex Edge : Type} (G : Graph Vertex Edge)

noncomputable def actualJoint (potential : SigningOutcome → Vertex → Bool) :
    PMF (RetainedHistory × (Vertex → Bits 8)) :=
  (retained signingHistory Outcome.state).map fun pair =>
    (pair, fun vertex => twist (potential pair.1 vertex)
      (RandomFunctionMACNativeCaller.Backend.tagBits (pair.2 7)))

theorem actual_joint_original (potential : SigningOutcome → Vertex → Bool) :
    (actualJoint potential).map Prod.fst = retained signingHistory Outcome.state := by
  simp only [actualJoint, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- The retained function marginal is exactly the original eager experiment,
not merely an independent posterior sample with the same endpoint law. -/
theorem actual_joint_eager (potential : SigningOutcome → Vertex → Bool) :
    (actualJoint potential).map Prod.fst =
      (uniform FunctionState).bind (fun function =>
        (RandomFunctionMACSchedules.Examples.attack.run (eager function) []).map
          (fun out => (out, function))) :=
  (actual_joint_original potential).trans actual_eager_marginal

/-- The common seed is the verification answer of the retained original
function. No independent replacement function is sampled for a vertex. -/
theorem actual_joint_projection (potential : SigningOutcome → Vertex → Bool) :
    (actualJoint potential).map (fun pair => (pair.1.1, pair.2)) =
      contextJoint G 8 signingHistory potential := by
  have law := congrArg
    (fun p => p.map (fun pair : SigningOutcome × Bits 8 =>
      (pair.1, fun vertex => twist (potential pair.1 vertex) pair.2))) actual_answer_law
  simpa only [actualJoint, contextJoint, tagJoint, PMF.map_comp, PMF.map_bind,
    Function.comp_def] using law

theorem actual_joint_realizes (potential : SigningOutcome → Vertex → Bool)
    (labels : SigningOutcome → Edge → Bool)
    (valid : ∀ past ∈ signingHistory.support, labels past = G.boundary (potential past)) :
    ContextRealizes G 8 signingHistory labels
      ((actualJoint potential).map (fun pair => (pair.1.1, pair.2))) := by
  rw [actual_joint_projection G]
  exact ⟨context_joint_history G 8 signingHistory potential,
    context_joint_vertex G 8 signingHistory potential,
    context_joint_edge G 8 signingHistory potential labels valid⟩

/-- Complete criterion including the full adaptive signing outcome. -/
theorem adaptive_joint_iff (labels : SigningOutcome → Edge → Bool) :
    (∃ candidate, ContextRealizes G 8 signingHistory labels candidate) ↔
      ∀ past ∈ signingHistory.support, G.Coherent (labels past) :=
  context_selected_joint_iff G 7 signingHistory labels

/-- Exactly n local triangle equations suffice for this family, at each
reachable signing history. No list of paths is supplied to the theorem. -/
theorem fan_faces_iff_joint (n : Nat) (labels : SigningOutcome → Fan.Edge n → Bool) :
    (∃ candidate, ContextRealizes (Fan.graph n) 8 signingHistory labels candidate) ↔
      ∀ past ∈ signingHistory.support, ∀ index : Fin n,
        labels past none = Bool.xor (labels past (some (index, false)))
          (labels past (some (index, true))) := by
  rw [adaptive_joint_iff]
  constructor
  · intro valid past supported
    exact (Fan.coherent_iff_faces n (labels past)).mp (valid past supported)
  · intro valid past supported
    exact (Fan.coherent_iff_faces n (labels past)).mpr (valid past supported)

/-- n additional selected correspondences are necessary and sufficient,
with the original function and complete signing outcome still retained. -/
theorem fan_minimum_repair (n : Nat) :
    ContextRealizes (Fan.graph n) 8 signingHistory (fun _ => Fan.repair)
      ((actualJoint (fun _ => Fan.potential)).map (fun pair => (pair.1.1, pair.2))) ∧
    Graph.repairCost Fan.weight Fan.initial (Fan.repair (n := n)) = n ∧
    ∀ labels : SigningOutcome → Fan.Edge n → Bool,
      (∀ past ∈ signingHistory.support, labels past none = true) →
      (∃ candidate, ContextRealizes (Fan.graph n) 8 signingHistory labels candidate) →
      ∀ past ∈ signingHistory.support, n ≤ Graph.repairCost Fan.weight Fan.initial (labels past) := by
  refine ⟨actual_joint_realizes (Fan.graph n) (fun _ => Fan.potential) (fun _ => Fan.repair)
    (fun _ _ => Fan.repaired_boundary n), Fan.repair_cost n, ?_⟩
  intro labels locked joint past supported
  exact Fan.repair_lower_bound n (labels past)
    ((adaptive_joint_iff (Fan.graph n) labels).mp joint past supported) (locked past supported)

/-- All individual edge endpoints remain uniform, but one changed edge
without repair has no common joint, even after conditioning on the history. -/
theorem fan_unrepaired_no_joint (n : Nat) (positive : 0 < n) :
    ¬∃ candidate, ContextRealizes (Fan.graph n) 8 signingHistory (fun _ => Fan.editedOnly) candidate := by
  intro joint
  obtain ⟨past, supported⟩ := signingHistory.support_nonempty
  have coherent := (adaptive_joint_iff (Fan.graph n) _).mp joint past supported
  exact Fan.editedOnly_no_joint n positive ((Fan.graph n).selected_joint_iff _ |>.mpr coherent)

end Foundation.Symmetric.RandomFunctionMACCouplingRepair
