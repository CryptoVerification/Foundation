import Foundation.Crypto.Logic.Polygraph.RootedTransport
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A fixed four-edge diagram with individually perfect marginal laws.
Its global deterministic-witness obstruction can encode any finite predicate.
The right branch forgets the input after adding its predicate to a uniform
mask. This is an obstruction of specified correspondences, not a claim that
the public marginal distributions are distinguishable. -/
namespace CryptoLogic.Polygraph.MaskedTransport

open Foundation.Probability RootedTransport
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Bit := ZMod 2

inductive Vertex where
  | root | left | right | tip
  deriving DecidableEq, Fintype

def State (Input : Type) : Vertex → Type
  | .root => Input × Bit
  | _ => Bit

inductive Edge : Vertex → Vertex → Type where
  | toLeft : Edge .root .left
  | toRight : Edge .root .right
  | leftTip : Edge .left .tip
  | rightTip : Edge .right .tip

def move {Input : Type} (predicate : Input → Bit) :
    ∀ source target, Edge source target → State Input source → State Input target
  | _, _, .toLeft => Prod.snd
  | _, _, .toRight => fun state => state.2 + predicate state.1
  | _, _, .leftTip => id
  | _, _, .rightTip => id

def route : ∀ vertex, Path Edge .root vertex
  | .root => .nil _
  | .left => .snoc (.nil _) .toLeft
  | .right => .snoc (.nil _) .toRight
  | .tip => .snoc (.snoc (.nil _) .toLeft) .leftTip

variable {Input : Type} [Fintype Input] [Nonempty Input]

theorem uniform_event_count (event : Input → Prop) [DecidablePred event] :
    eventProb (uniform Input) event =
      ((Finset.univ.filter event).card : ℝ≥0∞) * (Fintype.card Input : ℝ≥0∞)⁻¹ := by
  classical
  unfold eventProb
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, uniform, PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter]
  simp

noncomputable def law : ∀ vertex, PMF (State Input vertex)
  | .root => uniform (Input × Bit)
  | .left => uniform Bit
  | .right => uniform Bit
  | .tip => uniform Bit

theorem uniform_first : (uniform (Input × Bit)).map Prod.fst = uniform Input := by
  rw [← uniform_pair]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((uniform Input).bind fun a => (uniform Bit).map (Function.const Bit a)) = _
  simp only [PMF.map_const, PMF.bind_pure]

/-- Every edge is a valid coupling for every predicate, not just predicates
whose universal validity or satisfying assignments are already known. -/
theorem preserve (predicate : Input → Bit) {source target : Vertex} (edge : Edge source target) :
    (law source).map (move predicate source target edge) = law target := by
  cases edge with
  | toLeft =>
      change (uniform (Input × Bit)).map Prod.snd = uniform Bit
      rw [← uniform_pair]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      change ((uniform Input).bind fun _ => (uniform Bit).map id) = _
      rw [PMF.map_id, PMF.bind_const]
  | toRight =>
      change (uniform (Input × Bit)).map (fun state => state.2 + predicate state.1) = uniform Bit
      rw [← uniform_pair]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      have translate (input : Input) :
          (uniform Bit).map (fun mask => mask + predicate input) = uniform Bit :=
        uniform_map_equiv (Equiv.addRight (predicate input))
      simp_rw [translate]
      exact PMF.bind_const _ _
  | leftTip => exact PMF.map_id _
  | rightTip => exact PMF.map_id _

noncomputable def model (predicate : Input → Bit) : Model Vertex (State Input) where
  Edge := Edge
  root := .root
  move := move predicate
  law := law
  preserve := preserve predicate
  route := route
  route_root := by intro state; simp [route]

theorem compatible_iff (predicate : Input → Bit) (state : Input × Bit) :
    (model predicate).Compatible ((model predicate).canonical state) ↔ predicate state.1 = 0 := by
  constructor
  · intro compatible
    have h := compatible .right .tip .rightTip
    have he : state.2 = state.2 + predicate state.1 := by
      simpa only [model, Model.canonical, route, move, Path.run, State, id_eq] using h
    have cancel : state.2 + 0 = state.2 + predicate state.1 := by
      simpa only [add_zero] using he
    exact (add_left_cancel cancel).symm
  · intro zero source target edge
    cases edge <;> simp [model, Model.canonical, route, move, zero]

theorem bad_iff (predicate : Input → Bit) (state : Input × Bit) :
    (model predicate).Bad state ↔ predicate state.1 ≠ 0 :=
  not_congr (compatible_iff predicate state)

/-- The exact optimal obstruction is the probability of the encoded predicate.
Individual output laws remain uniform, including when this value is one. -/
theorem obstruction_probability (predicate : Input → Bit) :
    eventProb (model predicate).joint (fun a => ¬(model predicate).Compatible a) =
      eventProb (uniform Input) (fun input => predicate input ≠ 0) := by
  rw [(model predicate).joint_failure]
  have bad : (model predicate).Bad = (fun state => predicate state.1 ≠ 0) :=
    funext fun state => propext (bad_iff predicate state)
  rw [bad]
  change eventProb (uniform (Input × Bit)) (fun state => predicate state.1 ≠ 0) = _
  have mapped := eventProb_map (uniform (Input × Bit)) Prod.fst (fun input => predicate input ≠ 0)
  rw [uniform_first] at mapped
  exact mapped.symm

theorem unavoidable_obstruction (predicate : Input → Bit)
    (candidate : PMF (Model.Assignment (State := State Input)))
    (marginals : ∀ vertex, candidate.map (fun a => a vertex) = law vertex) :
    eventProb (uniform Input) (fun input => predicate input ≠ 0) ≤
      eventProb candidate (fun a => ¬(model predicate).Compatible a) := by
  rw [← obstruction_probability predicate, (model predicate).joint_failure]
  exact (model predicate).failure_lower_bound candidate (marginals .root)

theorem compatible_joint_iff (predicate : Input → Bit) :
    (∃ candidate : PMF (Model.Assignment (State := State Input)),
      (∀ vertex, candidate.map (fun a => a vertex) = law vertex) ∧
      ∀ a ∈ candidate.support, (model predicate).Compatible a) ↔
    ∀ input, predicate input = 0 := by
  change (∃ candidate : PMF (Model.Assignment (State := State Input)),
    (∀ vertex, candidate.map (fun a => a vertex) = (model predicate).law vertex) ∧
    ∀ a ∈ candidate.support, (model predicate).Compatible a) ↔ _
  rw [(model predicate).compatible_joint_iff]
  constructor
  · intro good input
    have h := good (input, 0) (by
      change (input, (0 : Bit)) ∈ (uniform (Input × Bit)).support
      exact PMF.mem_support_uniformOfFintype _)
    exact not_not.mp (by simpa only [bad_iff] using h)
  · intro zero state _
    simp only [bad_iff, zero state.1, ne_eq, not_true_eq_false, not_false_eq_true]

theorem same_vertex_laws (left right : Input → Bit) : (model left).law = (model right).law := rfl

/-- An information-loss result, not a proof-complexity lower bound. A method
that receives only the vertex marginal laws cannot decide this property,
regardless of the auxiliary lemmas or proof sharing it is allowed to use. -/
theorem no_marginal_only_checker :
    ¬∃ checker : (∀ vertex, PMF (State Input vertex)) → Bool,
      ∀ predicate : Input → Bit,
        checker (model predicate).law = true ↔ ∀ input, predicate input = 0 := by
  rintro ⟨checker, correct⟩
  have accepted := (correct (fun _ => 0)).mpr (fun _ => rfl)
  have impossible := (correct (fun _ => 1)).mp accepted
  have h := impossible (Classical.choice (inferInstance : Nonempty Input))
  norm_num at h

end CryptoLogic.Polygraph.MaskedTransport
