import Foundation.Crypto.Logic.Polygraph.RootedTransport

/-! An irreversible diamond: the root retains two independent fair bits,
while its two projections forget different bits. Every edge preserves the
correct vertex law, but preserving all four correspondences at once has an
unavoidable failure probability exactly one half. -/
namespace CryptoLogic.Polygraph.RootedTransport.Examples
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Vertex where
  | root | left | right | tip
  deriving DecidableEq

def State : Vertex → Type
  | .root => Bool × Bool
  | _ => Bool

inductive Edge : Vertex → Vertex → Type where
  | toLeft : Edge .root .left
  | toRight : Edge .root .right
  | leftTip : Edge .left .tip
  | rightTip : Edge .right .tip

def move : ∀ source target, Edge source target → State source → State target
  | _, _, .toLeft => Prod.fst
  | _, _, .toRight => Prod.snd
  | _, _, .leftTip => id
  | _, _, .rightTip => id

noncomputable def law : ∀ vertex, PMF (State vertex)
  | .root => uniform (Bool × Bool)
  | .left => uniform Bool
  | .right => uniform Bool
  | .tip => uniform Bool

theorem preserve {source target : Vertex} (edge : Edge source target) :
    (law source).map (move source target edge) = law target := by
  cases edge with
  | toLeft =>
      change (uniform (Bool × Bool)).map Prod.fst = uniform Bool
      rw [← uniform_pair]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      change ((uniform Bool).bind (fun a => (uniform Bool).map (Function.const Bool a))) = uniform Bool
      simp only [PMF.map_const, PMF.bind_pure]
  | toRight =>
      change (uniform (Bool × Bool)).map Prod.snd = uniform Bool
      rw [← uniform_pair]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      change ((uniform Bool).bind (fun _ => (uniform Bool).map id)) = uniform Bool
      rw [PMF.map_id, PMF.bind_const]
  | leftTip => exact PMF.map_id _
  | rightTip => exact PMF.map_id _

def route : ∀ vertex, Path Edge .root vertex
  | .root => .nil _
  | .left => .snoc (.nil _) .toLeft
  | .right => .snoc (.nil _) .toRight
  | .tip => .snoc (.snoc (.nil _) .toLeft) .leftTip

noncomputable def model : Model Vertex State where
  Edge := Edge
  root := .root
  move := move
  law := law
  preserve := preserve
  route := route
  route_root := by intro state; simp [route]

theorem projection_not_injective : ¬Function.Injective (move .root .left .toLeft) := by
  intro injective
  have h := injective (a₁ := (false, false)) (a₂ := (false, true)) rfl
  cases h

theorem compatible_iff (state : Bool × Bool) :
    model.Compatible (model.canonical state) ↔ state.1 = state.2 := by
  constructor
  · intro h
    have edge := h .right .tip .rightTip
    simpa [model, Model.canonical, route, move, Path.run] using edge
  · intro same source target edge
    cases edge <;> simp [model, Model.canonical, route, move, same]

theorem bad_probability : eventProb (model.law model.root) model.Bad = 1 / 2 := by
  have bad : model.Bad = (fun state : Bool × Bool => state.1 ≠ state.2) := by
    funext state
    exact propext (not_congr (compatible_iff state))
  rw [bad]
  change eventProb (uniform (Bool × Bool)) (fun state => state.1 ≠ state.2) = _
  rw [← uniform_pair, eventProb_bind_eq]
  simp only [eventProb_map]
  have conditional (a : Bool) : eventProb (uniform Bool) (fun b => a ≠ b) = 1 / 2 := by
    have equal : (fun b => a ≠ b) = (fun b => b = !a) := by
      funext b
      cases a <;> cases b <;> simp
    rw [equal, uniform_guess]
    norm_num
  simp only [conditional, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The optimum is achieved by a coupling with all correct vertex laws. -/
theorem optimal_failure : eventProb model.joint (fun assignment => ¬model.Compatible assignment) = 1 / 2 := by
  rw [model.joint_failure, bad_probability]

/-- Every alternative coupling, even with arbitrary correlations, must pay
at least this probability to realize all four chosen correspondences. -/
theorem unavoidable_failure (candidate : PMF (Model.Assignment (State := State)))
    (marginals : ∀ vertex, candidate.map (fun assignment => assignment vertex) = law vertex) :
    1 / 2 ≤ eventProb candidate (fun assignment => ¬model.Compatible assignment) := by
  rw [← bad_probability]
  exact model.failure_lower_bound candidate (marginals .root)

/-- The bound concerns simultaneous witness compatibility. It is not a
positive distinguishing advantage: each individual edge has its exact law. -/
theorem every_vertex_correct (vertex : Vertex) :
    model.joint.map (fun assignment => assignment vertex) = law vertex := model.joint_marginal vertex

end CryptoLogic.Polygraph.RootedTransport.Examples
