import Foundation.Crypto.Semantics.Probability.Facts

/-! Simultaneous realization of selected binary couplings. Each edge by
itself is an exact coupling of uniform games. Global realization is a separate
condition: its labels must be differences of vertex masks. No polygraph or
path-enumeration machinery is imported by this semantic baseline. -/
namespace Foundation.Probability.SelectedCouplingGraph
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

structure Graph (Vertex Edge : Type) where
  source : Edge → Vertex
  target : Edge → Vertex

variable {Vertex Edge : Type}

def xorEquiv (mask : Bool) : Bool ≃ Bool where
  toFun := Bool.xor mask
  invFun := Bool.xor mask
  left_inv := by intro bit; cases mask <;> cases bit <;> rfl
  right_inv := by intro bit; cases mask <;> cases bit <;> rfl

noncomputable def edgeLaw (mask : Bool) : PMF (Bool × Bool) :=
  (uniform Bool).map (fun bit => (bit, Bool.xor mask bit))

theorem edge_first (mask : Bool) : (edgeLaw mask).map Prod.fst = uniform Bool := by
  simp only [edgeLaw, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem edge_second (mask : Bool) : (edgeLaw mask).map Prod.snd = uniform Bool := by
  simp only [edgeLaw, PMF.map_comp, Function.comp_def]
  exact uniform_map_equiv (xorEquiv mask)

theorem edge_supported (mask : Bool) (pair : Bool × Bool) (supported : pair ∈ (edgeLaw mask).support) :
    pair.2 = Bool.xor mask pair.1 := by
  rw [edgeLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨bit, _, same⟩ := supported
  cases same
  rfl

namespace Graph
variable (G : Graph Vertex Edge)

def boundary (potential : Vertex → Bool) : Edge → Bool :=
  fun edge => Bool.xor (potential (G.source edge)) (potential (G.target edge))

def Coherent (labels : Edge → Bool) : Prop := ∃ potential, labels = G.boundary potential

def Compatible (labels : Edge → Bool) (assignment : Vertex → Bool) : Prop :=
  ∀ edge, assignment (G.target edge) = Bool.xor (labels edge) (assignment (G.source edge))

def Realizes (labels : Edge → Bool) (joint : PMF (Vertex → Bool)) : Prop :=
  (∀ vertex, joint.map (fun assignment => assignment vertex) = uniform Bool) ∧
  ∀ edge, joint.map (fun assignment => (assignment (G.source edge), assignment (G.target edge))) = edgeLaw (labels edge)

noncomputable def joint (_graph : Graph Vertex Edge) (potential : Vertex → Bool) : PMF (Vertex → Bool) :=
  (uniform Bool).map (fun bit vertex => Bool.xor (potential vertex) bit)

theorem joint_vertex (potential : Vertex → Bool) (vertex : Vertex) :
    (G.joint potential).map (fun assignment => assignment vertex) = uniform Bool := by
  simp only [joint, PMF.map_comp, Function.comp_def]
  exact uniform_map_equiv (xorEquiv (potential vertex))

theorem joint_edge (potential : Vertex → Bool) (edge : Edge) :
    (G.joint potential).map (fun assignment => (assignment (G.source edge), assignment (G.target edge))) =
      edgeLaw (G.boundary potential edge) := by
  unfold joint edgeLaw
  rw [PMF.map_comp]
  have parameter := uniform_map_equiv (xorEquiv (potential (G.source edge)))
  conv_rhs => rw [← parameter, PMF.map_comp]
  congr 1
  funext bit
  cases left : potential (G.source edge) <;> cases right : potential (G.target edge) <;> cases bit <;>
    simp [boundary, xorEquiv, left, right]

theorem realizes_compatible (labels : Edge → Bool) (candidate : PMF (Vertex → Bool))
    (realizes : G.Realizes labels candidate) (assignment : Vertex → Bool) (supported : assignment ∈ candidate.support) :
    G.Compatible labels assignment := by
  intro edge
  have pair : (assignment (G.source edge), assignment (G.target edge)) ∈ (edgeLaw (labels edge)).support := by
    rw [← realizes.2 edge, PMF.mem_support_map_iff]
    exact ⟨assignment, supported, rfl⟩
  exact edge_supported (labels edge) _ pair

theorem compatible_boundary (labels : Edge → Bool) (assignment : Vertex → Bool)
    (compatible : G.Compatible labels assignment) : labels = G.boundary assignment := by
  funext edge
  have relation := compatible edge
  cases left : assignment (G.source edge) <;> cases right : assignment (G.target edge) <;>
    cases mask : labels edge <;> simp_all [boundary]

/-- A common joint law realizes every selected edge coupling exactly iff
one consistent family of vertex masks exists. Endpoint marginals alone do
not imply this criterion. Disconnected vertices and self-edges are allowed. -/
theorem selected_joint_iff (labels : Edge → Bool) :
    (∃ candidate : PMF (Vertex → Bool), G.Realizes labels candidate) ↔ G.Coherent labels := by
  constructor
  · rintro ⟨candidate, realizes⟩
    obtain ⟨assignment, supported⟩ := candidate.support_nonempty
    exact ⟨assignment, G.compatible_boundary labels assignment
      (G.realizes_compatible labels candidate realizes assignment supported)⟩
  · rintro ⟨potential, rfl⟩
    exact ⟨G.joint potential, G.joint_vertex potential, G.joint_edge potential⟩

end Graph
end Foundation.Probability.SelectedCouplingGraph
