import Foundation.Logic.Polygraph.StateCube
import Foundation.Crypto.Logic.Polygraph.ExperimentSyntax

/-! One common probability space generated from coherent retained-state maps.
Correct individual marginal laws alone do not supply the local squares.
The common bad event is a separate hypothesis, never inferred from coherence. -/
namespace CryptoLogic.Polygraph

open Foundation.Logic.Polygraph Foundation.Probability
open scoped ENNReal

universe u v

namespace StateCube

variable {I : Type u} [DecidableEq I]

/-- Laws are supported on their declared vertices, and each fresh state map
pushes its source law to the prescribed target law. -/
structure Measured (C : Foundation.Logic.Polygraph.StateCube.{u, v} I) where
  law : Finset I → PMF C.State
  supported : ∀ S x, x ∈ (law S).support → C.vertex x = S
  preserve : ∀ S i, i ∉ S → (law S).map (C.step i) = law (insert i S)

variable {C : Foundation.Logic.Polygraph.StateCube.{u, v} I} (M : Measured C)

namespace Measured

/-- Lift genuinely different state spaces and their prescribed PMFs into the
total-space interface. Distribution preservation is required only on fresh
edges; the higher square certificates are separate arguments. -/
noncomputable def ofFamily (R : Finset I → Type v)
    (change : ∀ S i, R S → R (insert i S))
    (idle : ∀ S i x, i ∈ S → HEq (change S i x) x)
    (squares : ∀ S i j x, i ≠ j → i ∉ S → j ∉ S →
      HEq (change (insert i S) j (change S i x))
        (change (insert j S) i (change S j x)))
    (laws : ∀ S, PMF (R S))
    (preserve : ∀ S i, i ∉ S → (laws S).map (change S i) = laws (insert i S)) :
    Measured (Foundation.Logic.Polygraph.StateCube.ofFamily R change idle squares) where
  law S := (laws S).map (Sigma.mk S)
  supported S y hy := by
    obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    rfl
  preserve S i hi := by
    change ((laws S).map (Sigma.mk S)).map
      (fun x : Σ T, R T => Sigma.mk (insert i x.1) (change x.1 i x.2)) =
        (laws (insert i S)).map (Sigma.mk (insert i S))
    rw [PMF.map_comp]
    change (laws S).map ((Sigma.mk (insert i S)) ∘ (change S i)) = _
    rw [← PMF.map_comp, preserve S i hi]

/-- Build a model from one explicitly retained random source. Applications
with independently prescribed laws can instead use `Measured` directly. -/
noncomputable def fromRoot (C : Foundation.Logic.Polygraph.StateCube.{u, v} I)
    (root : PMF C.State) (supported : ∀ x ∈ root.support, C.vertex x = ∅) : Measured C where
  law S := root.map (fun x => C.query x S)
  supported S y hy := by
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    rw [C.vertex_query, supported x hx, Finset.empty_union]
  preserve S i _ := by
    rw [PMF.map_comp]
    congr 1
    funext x
    exact (C.query_insert x S i).symm

theorem fromRoot_empty (C : Foundation.Logic.Polygraph.StateCube.{u, v} I)
    (root : PMF C.State) (supported : ∀ x ∈ root.support, C.vertex x = ∅) :
    (fromRoot C root supported).law ∅ = root := by
  simp only [fromRoot, C.query_empty]
  exact PMF.map_id _

/-- Every query has exactly the prescribed law, using the same root sample. -/
theorem query_law (S : Finset I) :
    (M.law ∅).map (fun x => C.query x S) = M.law S := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [C.query_empty]
    exact PMF.map_id _
  | @insert i S hi ih =>
    simp_rw [C.query_insert]
    change (M.law ∅).map ((C.step i) ∘ (fun x => C.query x S)) = _
    rw [← PMF.map_comp, ih, M.preserve S i hi]

/-- A sample is a function of the vertex. No enumeration of the vertices is
needed to evaluate one component. The PMF is a mathematical joint law. -/
noncomputable def joint : PMF (Finset I → C.State) :=
  (M.law ∅).map (fun x S => C.query x S)

theorem joint_marginal (S : Finset I) :
    M.joint.map (fun assignment => assignment S) = M.law S := by
  rw [joint, PMF.map_comp]
  exact M.query_law S

/-- All edge equations hold on every reachable joint sample, at once. -/
theorem joint_edges (assignment : Finset I → C.State)
    (ha : assignment ∈ M.joint.support) :
    ∀ S i, assignment (insert i S) = C.step i (assignment S) := by
  obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact C.query_insert x

theorem joint_vertices (assignment : Finset I → C.State)
    (ha : assignment ∈ M.joint.support) :
    ∀ S, C.vertex (assignment S) = S := by
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  intro S
  rw [C.vertex_query, M.supported ∅ x hx, Finset.empty_union]

/-- The joint law realizes each specified deterministic edge coupling,
including its hidden state correspondence, not just its two marginals. -/
theorem joint_edge_law (S : Finset I) (i : I) :
    M.joint.map (fun a => (a S, a (insert i S))) =
      (M.law S).map (fun x => (x, C.step i x)) := by
  rw [joint, PMF.map_comp, ← M.query_law S, PMF.map_comp]
  congr 1
  funext x
  simp [C.query_insert]

/-- A common realization with these deterministic edges and root law is
unique. This concerns the selected correspondences, not just output laws. -/
theorem joint_unique (p : PMF (Finset I → C.State))
    (root : p.map (fun a => a ∅) = M.law ∅)
    (edges : ∀ a ∈ p.support, ∀ S i, a (insert i S) = C.step i (a S)) :
    p = M.joint := by
  have rebuild : p.map (fun a S => C.query (a ∅) S) = p := by
    calc
      _ = p.map id := by
        unfold PMF.map
        apply bind_congr_of_support
        intro a ha
        apply congrArg PMF.pure
        funext S
        exact (C.assignment_unique a (edges a ha) S).symm
      _ = p := PMF.map_id _
  calc
    p = p.map (fun a S => C.query (a ∅) S) := rebuild.symm
    _ = (p.map (fun a => a ∅)).map (fun x S => C.query x S) :=
      (PMF.map_comp (fun a : Finset I → C.State => a ∅) p
        (fun x S => C.query x S)).symm
    _ = M.joint := by rw [root]; rfl

/-- Observations propagate through the cube outside one shared bad event.
The assumption explicitly refers to the same root sample on every edge. -/
theorem observations_agree (event : Finset I → C.State → Prop)
    (bad : C.State → Prop)
    (edge : ∀ x ∈ (M.law ∅).support, ¬bad x → ∀ S i, i ∉ S →
      (event S (C.query x S) ↔ event (insert i S) (C.step i (C.query x S))))
    (x : C.State) (hx : x ∈ (M.law ∅).support) (hb : ¬bad x) (S : Finset I) :
    event ∅ x ↔ event S (C.query x S) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [C.query_insert]
    exact ih.trans (edge x hx hb S i hi)

/-- A single bad probability, rather than a sum over an arbitrary route. -/
theorem common_bad_bound (event : Finset I → C.State → Prop)
    (bad : C.State → Prop)
    (edge : ∀ x ∈ (M.law ∅).support, ¬bad x → ∀ S i, i ∉ S →
      (event S (C.query x S) ↔ event (insert i S) (C.step i (C.query x S))))
    (S : Finset I) :
    probabilityGap (eventProb (M.law ∅) (event ∅))
      (eventProb (M.law S) (event S)) ≤ eventProb (M.law ∅) bad := by
  exact coupled_map_gap_le (M.law ∅) (M.law ∅) (M.law S) id
    (fun x => C.query x S) (PMF.map_id _) (M.query_law S) _ _ bad
    (fun x hx hb => M.observations_agree event bad edge x hx hb S)

/-- The same shared failure event also compares any two intermediate games. -/
theorem common_bad_between (event : Finset I → C.State → Prop)
    (bad : C.State → Prop)
    (edge : ∀ x ∈ (M.law ∅).support, ¬bad x → ∀ S i, i ∉ S →
      (event S (C.query x S) ↔ event (insert i S) (C.step i (C.query x S))))
    (S T : Finset I) :
    probabilityGap (eventProb (M.law S) (event S))
      (eventProb (M.law T) (event T)) ≤ eventProb (M.law ∅) bad := by
  apply coupled_map_gap_le (M.law ∅) (M.law S) (M.law T)
    (fun x => C.query x S) (fun x => C.query x T) (M.query_law S) (M.query_law T)
    _ _ bad
  intro x hx hb
  exact (M.observations_agree event bad edge x hx hb S).symm.trans
    (M.observations_agree event bad edge x hx hb T)

/-- The constructed common realization is also a certificate in the existing
statistical game-hop syntax. It can be composed with other certified hops. -/
noncomputable def commonBadHop (event : Finset I → C.State → Prop)
    (bad : C.State → Prop)
    (edge : ∀ x ∈ (M.law ∅).support, ¬bad x → ∀ S i, i ∉ S →
      (event S (C.query x S) ↔ event (insert i S) (C.step i (C.query x S))))
    (S : Finset I) :
    Experiment.Hop ⟨C.State, .sample (M.law ∅), event ∅⟩
      ⟨C.State, .sample (M.law S), event S⟩ (eventProb (M.law ∅) bad) :=
  .coupling (M.law ∅) id (fun x => C.query x S) (PMF.map_id _) (M.query_law S)
    bad (fun x hx hb => M.observations_agree event bad edge x hx hb S)

end Measured
end StateCube
end CryptoLogic.Polygraph
