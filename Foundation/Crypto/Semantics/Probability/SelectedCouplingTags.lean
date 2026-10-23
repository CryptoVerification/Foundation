import Foundation.Crypto.Semantics.Probability.SelectedCouplingRepair
import Foundation.Constructions.Symmetric.OneTimePad

/-! Lift selected binary mask correspondences to entire nonempty bitstring
responses. The first bit reflects inconsistency, while every edge remains an
exact coupling of uniform full tags. This imports no proof-diagram syntax. -/
namespace Foundation.Probability.SelectedCouplingGraph
open Foundation.Symmetric
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Vertex Edge : Type} (G : Graph Vertex Edge)

def twist {width : Nat} (mask : Bool) (tag : Bits width) : Bits width :=
  fun index => Bool.xor mask (tag index)

def twistEquiv (width : Nat) (mask : Bool) : Bits width ≃ Bits width where
  toFun := twist mask
  invFun := twist mask
  left_inv := by intro tag; funext index; simp only [twist]; cases mask <;> cases tag index <;> rfl
  right_inv := by intro tag; funext index; simp only [twist]; cases mask <;> cases tag index <;> rfl

noncomputable def tagEdge (width : Nat) (mask : Bool) : PMF (Bits width × Bits width) :=
  (uniform (Bits width)).map (fun tag => (tag, twist mask tag))

noncomputable def tagJoint (_graph : Graph Vertex Edge) (width : Nat) (potential : Vertex → Bool) : PMF (Vertex → Bits width) :=
  (uniform (Bits width)).map (fun tag vertex => twist (potential vertex) tag)

def TagRealizes (width : Nat) (labels : Edge → Bool) (candidate : PMF (Vertex → Bits width)) : Prop :=
  (∀ vertex, candidate.map (fun assignment => assignment vertex) = uniform (Bits width)) ∧
  ∀ edge, candidate.map (fun assignment => (assignment (G.source edge), assignment (G.target edge))) = tagEdge width (labels edge)

theorem tag_first (width : Nat) (mask : Bool) : (tagEdge width mask).map Prod.fst = uniform (Bits width) := by
  simp only [tagEdge, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem tag_second (width : Nat) (mask : Bool) : (tagEdge width mask).map Prod.snd = uniform (Bits width) := by
  simp only [tagEdge, PMF.map_comp, Function.comp_def]
  exact uniform_map_equiv (twistEquiv width mask)

theorem tag_joint_vertex (width : Nat) (potential : Vertex → Bool) (vertex : Vertex) :
    (tagJoint G width potential).map (fun assignment => assignment vertex) = uniform (Bits width) := by
  simp only [tagJoint, PMF.map_comp, Function.comp_def]
  exact uniform_map_equiv (twistEquiv width (potential vertex))

theorem tag_joint_edge (width : Nat) (potential : Vertex → Bool) (edge : Edge) :
    (tagJoint G width potential).map (fun assignment => (assignment (G.source edge), assignment (G.target edge))) =
      tagEdge width (G.boundary potential edge) := by
  unfold tagJoint tagEdge
  rw [PMF.map_comp]
  have parameter := uniform_map_equiv (twistEquiv width (potential (G.source edge)))
  conv_rhs => rw [← parameter, PMF.map_comp]
  congr 1
  funext tag
  apply Prod.ext
  · rfl
  · funext index
    change twist (potential (G.target edge)) tag index =
      twist (G.boundary potential edge) (twist (potential (G.source edge)) tag) index
    simp only [Graph.boundary, twist]
    cases potential (G.source edge) <;> cases potential (G.target edge) <;> cases tag index <;> rfl

/-- For full tags, simultaneous realization has exactly the same criterion.
Positive width is essential: empty tags cannot distinguish the two masks. -/
theorem tag_selected_joint_iff (width : Nat) (labels : Edge → Bool) :
    (∃ candidate : PMF (Vertex → Bits (width + 1)), TagRealizes G (width + 1) labels candidate) ↔ G.Coherent labels := by
  constructor
  · rintro ⟨candidate, realizes⟩
    obtain ⟨assignment, supported⟩ := candidate.support_nonempty
    apply Exists.intro (fun vertex => assignment vertex 0)
    apply G.compatible_boundary
    intro edge
    have pair : (assignment (G.source edge), assignment (G.target edge)) ∈ (tagEdge (width + 1) (labels edge)).support := by
      rw [← realizes.2 edge, PMF.mem_support_map_iff]
      exact ⟨assignment, supported, rfl⟩
    rw [tagEdge, PMF.mem_support_map_iff] at pair
    obtain ⟨tag, _, same⟩ := pair
    have first : tag = assignment (G.source edge) := congrArg Prod.fst same
    have second : twist (labels edge) tag = assignment (G.target edge) := congrArg Prod.snd same
    change assignment (G.target edge) 0 = Bool.xor (labels edge) (assignment (G.source edge) 0)
    rw [← second, ← first]
    rfl
  · rintro ⟨potential, rfl⟩
    exact ⟨tagJoint G (width + 1) potential, tag_joint_vertex G (width + 1) potential, tag_joint_edge G (width + 1) potential⟩

variable [Fintype Edge]

theorem tag_repair_cost_iff (width : Nat) (weight : Edge → Nat) (original : Vertex → Bool)
    (locked : Edge) (cost : Nat) :
    (∃ updated, ∃ candidate : PMF (Vertex → Bits (width + 1)), TagRealizes G (width + 1) updated candidate ∧
      updated locked ≠ G.boundary original locked ∧ Graph.repairCost weight (G.boundary original) updated = cost) ↔
    (∃ cut : Vertex → Bool, cut (G.source locked) ≠ cut (G.target locked) ∧ G.cutCost weight cut = cost) := by
  rw [← G.feasible_cost_iff weight original locked cost]
  constructor
  · rintro ⟨updated, candidate, realizes, changed, price⟩
    exact ⟨updated, ⟨(tag_selected_joint_iff G width updated).mp ⟨candidate, realizes⟩, changed⟩, price⟩
  · rintro ⟨updated, ⟨coherent, changed⟩, price⟩
    obtain ⟨candidate, realizes⟩ := (tag_selected_joint_iff G width updated).mpr coherent
    exact ⟨updated, candidate, realizes, changed, price⟩

end Foundation.Probability.SelectedCouplingGraph
