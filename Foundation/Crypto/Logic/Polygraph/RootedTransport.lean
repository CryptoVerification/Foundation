import Foundation.Crypto.Semantics.Probability.Facts

/-! Quantitative compatibility for prescribed deterministic state transports.
States may have different types, and transports need not be injective.
A chosen directed path from the root supplies each canonical state. Every
joint realization with the same root law must fail on every incompatible
root; the canonical realization attains that lower bound while preserving
all vertex laws. This measures compatibility of chosen witnesses, not the
security advantage of the experiments. -/
namespace CryptoLogic.Polygraph.RootedTransport
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
universe u v w

inductive Path {Vertex : Type u} (Edge : Vertex → Vertex → Type v) : Vertex → Vertex → Type (max u v) where
  | nil (vertex : Vertex) : Path Edge vertex vertex
  | snoc {root source target : Vertex} : Path Edge root source → Edge source target → Path Edge root target

namespace Path
variable {Vertex : Type u} {Edge : Vertex → Vertex → Type v} {State : Vertex → Type w}

def run (move : ∀ source target, Edge source target → State source → State target) :
    {source target : Vertex} → Path Edge source target → State source → State target
  | _, _, .nil _, state => state
  | _, _, .snoc path edge, state => move _ _ edge (run move path state)

@[simp] theorem run_nil (move : ∀ source target, Edge source target → State source → State target)
    (source : Vertex) : run move (.nil source) = id := by
  funext state
  simp [run]

@[simp] theorem run_snoc (move : ∀ source target, Edge source target → State source → State target)
    {root source target : Vertex} (path : Path Edge root source) (edge : Edge source target) :
    run move (.snoc path edge) = move _ _ edge ∘ run move path := by
  funext state
  simp [run]

end Path

structure Model (Vertex : Type u) (State : Vertex → Type w) where
  Edge : Vertex → Vertex → Type v
  root : Vertex
  move : ∀ source target, Edge source target → State source → State target
  law : ∀ vertex, PMF (State vertex)
  preserve : ∀ {source target} (edge : Edge source target), (law source).map (move _ _ edge) = law target
  route : ∀ vertex, Path Edge root vertex
  route_root : ∀ state, Path.run move (route root) state = state

namespace Model
variable {Vertex : Type u} {State : Vertex → Type w} (M : Model.{u, v, w} Vertex State)

abbrev Assignment := ∀ vertex, State vertex

def canonical (state : State M.root) : Assignment (State := State) :=
  fun vertex => Path.run M.move (M.route vertex) state

def Compatible (assignment : Assignment (State := State)) : Prop :=
  ∀ source target (edge : M.Edge source target), assignment target = M.move _ _ edge (assignment source)

def Bad (state : State M.root) : Prop := ¬M.Compatible (M.canonical state)

/-- The root determines every globally compatible assignment, including
assignments obtained through irreversible or type-changing transports. -/
theorem reconstruct (assignment : Assignment (State := State)) (h : M.Compatible assignment)
    (vertex : Vertex) : assignment vertex = M.canonical (assignment M.root) vertex := by
  have along {source target : Vertex} (path : Path M.Edge source target) :
      assignment target = Path.run M.move path (assignment source) := by
    induction path with
    | nil => simp only [Path.run_nil, id_eq]
    | snoc path edge ih => rw [Path.run_snoc, Function.comp_apply, h _ _ edge, ih]
  exact along (M.route vertex)

theorem bad_forces_failure (assignment : Assignment (State := State))
    (h : M.Bad (assignment M.root)) : ¬M.Compatible assignment := by
  intro compatible
  have same : assignment = M.canonical (assignment M.root) := funext (M.reconstruct assignment compatible)
  exact h (same ▸ compatible)

theorem route_law {source target : Vertex} (path : Path M.Edge source target) :
    (M.law source).map (Path.run M.move path) = M.law target := by
  induction path with
  | nil => simpa only [Path.run_nil] using PMF.map_id (M.law _)
  | snoc path edge ih =>
      rw [Path.run_snoc, ← PMF.map_comp, ih, M.preserve edge]

noncomputable def joint : PMF (Assignment (State := State)) :=
  (M.law M.root).map M.canonical

theorem joint_marginal (vertex : Vertex) :
    M.joint.map (fun assignment => assignment vertex) = M.law vertex := by
  rw [joint, PMF.map_comp]
  exact M.route_law (M.route vertex)

/-- Exact obstruction probability of the canonical joint realization. -/
theorem joint_failure : eventProb M.joint (fun assignment => ¬M.Compatible assignment) =
    eventProb (M.law M.root) M.Bad := by
  rw [joint, eventProb_map]
  rfl

/-- No other coupling can improve the probability that all prescribed
transports hold simultaneously. Only its root marginal is needed here. -/
theorem failure_lower_bound (candidate : PMF (Assignment (State := State)))
    (root_law : candidate.map (fun assignment => assignment M.root) = M.law M.root) :
    eventProb (M.law M.root) M.Bad ≤ eventProb candidate (fun assignment => ¬M.Compatible assignment) := by
  rw [← root_law, eventProb_map]
  exact eventProb_mono _ (fun assignment => M.bad_forces_failure assignment)

/-- The lower bound is attained by a coupling with every correct vertex
marginal. Thus this is an optimum, not merely an obstruction estimate. -/
theorem failure_optimal :
    (∀ vertex, M.joint.map (fun assignment => assignment vertex) = M.law vertex) ∧
    eventProb M.joint (fun assignment => ¬M.Compatible assignment) = eventProb (M.law M.root) M.Bad ∧
    ∀ candidate : PMF (Assignment (State := State)),
      (∀ vertex, candidate.map (fun assignment => assignment vertex) = M.law vertex) →
      eventProb M.joint (fun assignment => ¬M.Compatible assignment) ≤
        eventProb candidate (fun assignment => ¬M.Compatible assignment) := by
  refine ⟨M.joint_marginal, M.joint_failure, ?_⟩
  intro candidate marginals
  rw [M.joint_failure]
  exact M.failure_lower_bound candidate (marginals M.root)

/-- Exact existence criterion for a joint law realizing every selected
edge correspondence, rather than merely matching endpoint distributions. -/
theorem compatible_joint_iff :
    (∃ candidate : PMF (Assignment (State := State)),
      (∀ vertex, candidate.map (fun assignment => assignment vertex) = M.law vertex) ∧
      ∀ assignment ∈ candidate.support, M.Compatible assignment) ↔
    ∀ state ∈ (M.law M.root).support, ¬M.Bad state := by
  constructor
  · rintro ⟨candidate, marginals, compatible⟩ state hs
    rw [← marginals M.root, PMF.mem_support_map_iff] at hs
    obtain ⟨assignment, ha, rfl⟩ := hs
    intro bad
    exact M.bad_forces_failure assignment bad (compatible assignment ha)
  · intro good
    refine ⟨M.joint, M.joint_marginal, ?_⟩
    intro assignment ha
    rw [joint, PMF.mem_support_map_iff] at ha
    obtain ⟨state, hs, rfl⟩ := ha
    exact Classical.not_not.mp (good state hs)

/-- When compatible, the joint law is forced by the root law. -/
theorem joint_unique (candidate : PMF (Assignment (State := State)))
    (root_law : candidate.map (fun assignment => assignment M.root) = M.law M.root)
    (compatible : ∀ assignment ∈ candidate.support, M.Compatible assignment) : candidate = M.joint := by
  have rebuild : candidate.map (fun assignment => M.canonical (assignment M.root)) = candidate := by
    calc
      _ = candidate.map id := by
        unfold PMF.map
        apply bind_congr_of_support
        intro assignment ha
        exact congrArg PMF.pure (funext (M.reconstruct assignment (compatible assignment ha))).symm
      _ = _ := PMF.map_id _
  calc
    candidate = candidate.map (fun assignment => M.canonical (assignment M.root)) := rebuild.symm
    _ = (candidate.map (fun assignment => assignment M.root)).map M.canonical :=
      (PMF.map_comp (fun assignment : Assignment (State := State) => assignment M.root) candidate M.canonical).symm
    _ = M.joint := by rw [root_law]; rfl

/-- The optimum is independent of the chosen root-to-vertex routes.
Both systems must retain the same prescribed edge constraints. -/
theorem route_independent (other : Model.{u, v, w} Vertex State)
    (same_law : other.law = M.law)
    (same_constraints : ∀ assignment, other.Compatible assignment ↔ M.Compatible assignment) :
    eventProb (M.law M.root) M.Bad = eventProb (other.law other.root) other.Bad := by
  have first := M.failure_lower_bound other.joint (by
    rw [other.joint_marginal, same_law])
  have second := other.failure_lower_bound M.joint (by
    rw [M.joint_marginal, same_law])
  have first_event : eventProb other.joint (fun a => ¬M.Compatible a) =
      eventProb other.joint (fun a => ¬other.Compatible a) := by
    congr 1
    funext assignment
    exact propext (not_congr (same_constraints assignment).symm)
  have second_event : eventProb M.joint (fun a => ¬other.Compatible a) =
      eventProb M.joint (fun a => ¬M.Compatible a) := by
    congr 1
    funext assignment
    exact propext (not_congr (same_constraints assignment))
  rw [first_event, other.joint_failure] at first
  rw [second_event, M.joint_failure] at second
  exact le_antisymm first second

end Model
end CryptoLogic.Polygraph.RootedTransport
