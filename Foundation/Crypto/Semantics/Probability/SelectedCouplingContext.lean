import Foundation.Crypto.Semantics.Probability.SelectedCouplingTags

/-! Exact simultaneous realization after an observed, possibly adaptive history.
The context is retained in each edge law. No independence of the selected masks
from that context is assumed. This module imports no proof-diagram syntax. -/
namespace Foundation.Probability.SelectedCouplingGraph
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

variable {Vertex Edge Context : Type} (G : Graph Vertex Edge)

noncomputable def contextEdge (width : Nat) (history : PMF Context)
    (labels : Context → Edge → Bool) (edge : Edge) : PMF (Context × (Bits width × Bits width)) :=
  history.bind fun past => (tagEdge width (labels past edge)).map fun pair => (past, pair)

noncomputable def contextJoint (width : Nat) (history : PMF Context)
    (potential : Context → Vertex → Bool) : PMF (Context × (Vertex → Bits width)) :=
  history.bind fun past => (tagJoint G width (potential past)).map fun assignment => (past, assignment)

def ContextRealizes (width : Nat) (history : PMF Context) (labels : Context → Edge → Bool)
    (candidate : PMF (Context × (Vertex → Bits width))) : Prop :=
  candidate.map Prod.fst = history ∧
  (∀ vertex, candidate.map (fun pair => (pair.1, pair.2 vertex)) =
    history.bind fun past => (uniform (Bits width)).map fun tag => (past, tag)) ∧
  ∀ edge, candidate.map (fun pair => (pair.1, (pair.2 (G.source edge), pair.2 (G.target edge)))) =
    contextEdge width history labels edge

theorem context_joint_history (width : Nat) (history : PMF Context) (potential : Context → Vertex → Bool) :
    (contextJoint G width history potential).map Prod.fst = history := by
  simp only [contextJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (history.bind fun past => (tagJoint G width (potential past)).map (Function.const _ past)) = history
  simp only [PMF.map_const, PMF.bind_pure]

theorem context_joint_vertex (width : Nat) (history : PMF Context)
    (potential : Context → Vertex → Bool) (vertex : Vertex) :
    (contextJoint G width history potential).map (fun pair => (pair.1, pair.2 vertex)) =
      history.bind fun past => (uniform (Bits width)).map fun tag => (past, tag) := by
  simp only [contextJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext past
  have law := congrArg (fun p => p.map (fun tag => (past, tag)))
    (tag_joint_vertex G width (potential past) vertex)
  simpa only [PMF.map_comp, Function.comp_def] using law

theorem context_joint_edge (width : Nat) (history : PMF Context)
    (potential : Context → Vertex → Bool) (labels : Context → Edge → Bool)
    (valid : ∀ past ∈ history.support, labels past = G.boundary (potential past)) (edge : Edge) :
    (contextJoint G width history potential).map
      (fun pair => (pair.1, (pair.2 (G.source edge), pair.2 (G.target edge)))) =
      contextEdge width history labels edge := by
  simp only [contextJoint, contextEdge, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_of_support
  intro past supported
  rw [valid past supported]
  have law := congrArg (fun p => p.map (fun pair => (past, pair)))
    (tag_joint_edge G width (potential past) edge)
  simpa only [PMF.map_comp, Function.comp_def] using law

/-- The same joint must retain the history in every selected edge law.
Individual unconditional edge marginals are not the contract. -/
theorem context_selected_joint_iff (width : Nat) (history : PMF Context)
    (labels : Context → Edge → Bool) :
    (∃ candidate, ContextRealizes G (width + 1) history labels candidate) ↔
      ∀ past ∈ history.support, G.Coherent (labels past) := by
  classical
  constructor
  · rintro ⟨candidate, realizes⟩ past reachable
    rw [← realizes.1, PMF.mem_support_map_iff] at reachable
    obtain ⟨pair, supported, same⟩ := reachable
    obtain ⟨past', assignment⟩ := pair
    change past' = past at same
    subst past'
    apply Exists.intro (fun vertex => assignment vertex 0)
    apply G.compatible_boundary
    intro edge
    have edgeSupported : (past, (assignment (G.source edge), assignment (G.target edge))) ∈
        (contextEdge (width + 1) history labels edge).support := by
      rw [← realizes.2.2 edge, PMF.mem_support_map_iff]
      exact ⟨(past, assignment), supported, rfl⟩
    rw [contextEdge, PMF.mem_support_bind_iff] at edgeSupported
    obtain ⟨other, _, edgeSupported⟩ := edgeSupported
    rw [PMF.mem_support_map_iff] at edgeSupported
    obtain ⟨tags, tagsSupported, tagsSame⟩ := edgeSupported
    have historySame : other = past := congrArg Prod.fst tagsSame
    subst other
    have pairSame : tags = (assignment (G.source edge), assignment (G.target edge)) := congrArg Prod.snd tagsSame
    subst tags
    rw [tagEdge, PMF.mem_support_map_iff] at tagsSupported
    obtain ⟨tag, _, tagSame⟩ := tagsSupported
    have first : tag = assignment (G.source edge) := congrArg Prod.fst tagSame
    have second : twist (labels past edge) tag = assignment (G.target edge) := congrArg Prod.snd tagSame
    change assignment (G.target edge) 0 = Bool.xor (labels past edge) (assignment (G.source edge) 0)
    rw [← second, ← first]
    rfl
  · intro valid
    let potential : Context → Vertex → Bool := fun past =>
      if supported : past ∈ history.support then (valid past supported).choose else fun _ => false
    have agreement : ∀ past ∈ history.support, labels past = G.boundary (potential past) := by
      intro past supported
      simp only [potential, dif_pos supported]
      exact (valid past supported).choose_spec
    exact ⟨contextJoint G (width + 1) history potential,
      context_joint_history G (width + 1) history potential,
      context_joint_vertex G (width + 1) history potential,
      context_joint_edge G (width + 1) history potential labels agreement⟩

/-- A history-dependent repair with prescribed pointwise costs exists exactly
when every reachable history admits a separating cut of that cost. This is an
existence and cost theorem, not a verified minimum-cut implementation. -/
theorem context_repair_cost_iff [Fintype Edge] (width : Nat) (history : PMF Context)
    (weight : Context → Edge → Nat) (original : Context → Vertex → Bool)
    (locked : Context → Edge) (cost : Context → Nat) :
    (∃ updated : Context → Edge → Bool,
      (∃ candidate, ContextRealizes G (width + 1) history updated candidate) ∧
      ∀ past ∈ history.support,
        updated past (locked past) ≠ G.boundary (original past) (locked past) ∧
        Graph.repairCost (weight past) (G.boundary (original past)) (updated past) = cost past) ↔
    (∀ past ∈ history.support, ∃ cut : Vertex → Bool,
      cut (G.source (locked past)) ≠ cut (G.target (locked past)) ∧
      G.cutCost (weight past) cut = cost past) := by
  classical
  constructor
  · rintro ⟨updated, joint, conditions⟩ past supported
    apply (G.feasible_cost_iff (weight past) (original past) (locked past) (cost past)).mp
    exact ⟨updated past,
      ⟨(context_selected_joint_iff G width history updated).mp joint past supported,
        (conditions past supported).1⟩, (conditions past supported).2⟩
  · intro cuts
    have feasible : ∀ past ∈ history.support, ∃ updated : Edge → Bool,
        G.Feasible (G.boundary (original past)) (locked past) updated ∧
        Graph.repairCost (weight past) (G.boundary (original past)) updated = cost past := by
      intro past supported
      exact (G.feasible_cost_iff (weight past) (original past) (locked past) (cost past)).mpr
        (cuts past supported)
    let updated : Context → Edge → Bool := fun past =>
      if supported : past ∈ history.support then (feasible past supported).choose
      else G.boundary (original past)
    have property : ∀ past ∈ history.support,
        G.Feasible (G.boundary (original past)) (locked past) (updated past) ∧
        Graph.repairCost (weight past) (G.boundary (original past)) (updated past) = cost past := by
      intro past supported
      simp only [updated, dif_pos supported]
      exact (feasible past supported).choose_spec
    refine ⟨updated, (context_selected_joint_iff G width history updated).mpr ?_, ?_⟩
    · intro past supported
      exact (property past supported).1.1
    · intro past supported
      exact ⟨(property past supported).1.2, (property past supported).2⟩

end Foundation.Probability.SelectedCouplingGraph
