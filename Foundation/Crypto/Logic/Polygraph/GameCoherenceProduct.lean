import Foundation.Crypto.Logic.Polygraph.GameCoherence

/-! Independent probabilistic contexts and higher interchange. Product games
run both computations independently; copying an already sampled state is a
different transformation and is not interpreted by this product operation. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence
open Foundation.Probability
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

def product (first second : Observed.{u}) : Observed.{u} where
  Outcome := first.Outcome × second.Outcome
  program := .bind first.program (fun x => second.program.map (fun y => (x, y)))
  event pair := first.event pair.1 ∧ second.event pair.2

theorem product_left (first second : Observed.{u}) :
    (product first second).program.eval.map Prod.fst = first.program.eval := by
  simp only [product, Program.eval, eval_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (first.program.eval.bind fun x => second.program.eval.map
    (Function.const second.Outcome x)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem product_right (first second : Observed.{u}) :
    (product first second).program.eval.map Prod.snd = second.program.eval := by
  simp only [product, Program.eval, eval_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (first.program.eval.bind fun _ => second.program.eval.map id) = _
  rw [PMF.map_id, PMF.bind_const]

theorem product_swap (first second : Observed.{u}) :
    (product first second).program.eval.map Prod.swap = (product second first).program.eval := by
  simp only [product, Program.eval, eval_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

namespace Step
variable {a b : Observed.{u}}

def swap (first second : Observed.{u}) : Step (product first second) (product second first) :=
  ofMap _ _ Prod.swap (product_swap first second) (fun _ _ => and_comm)

def leftKernel (step : Step a b) (context : Observed.{u}) :
    (product a context).Outcome → PMF (product b context).Outcome :=
  fun state => (step.kernel state.1).map fun next => (next, state.2)

theorem left_preserve (step : Step a b) (context : Observed.{u}) :
    (product a context).program.eval.bind (step.leftKernel context) =
      (product b context).program.eval := by
  change (a.program.eval.bind fun x => context.program.eval.map (fun c => (x, c))).bind
    (step.leftKernel context) = _
  simp only [PMF.bind_bind, PMF.bind_map, leftKernel, Function.comp_def]
  have exchange (x : a.Outcome) :
      context.program.eval.bind (fun c => (step.kernel x).map fun y => (y, c)) =
        (step.kernel x).bind (fun y => context.program.eval.map fun c => (y, c)) :=
    PMF.bind_comm _ _ _
  simp_rw [exchange]
  rw [← PMF.bind_bind, step.preserve]
  rfl

theorem left_joint_project (step : Step a b) (context : Observed.{u}) :
    ((product a context).program.eval.bind (fun x =>
      (step.leftKernel context x).map (fun y => (x, y)))).map
        (fun pair => (pair.1.1, pair.2.1)) = step.joint := by
  simp only [product, Program.eval, eval_map, PMF.map_bind, PMF.map_comp,
    PMF.bind_bind, PMF.bind_map, leftKernel, Function.comp_def]
  simp only [PMF.bind_const]
  rfl

def left (step : Step a b) (context : Observed.{u}) : Step (product a context) (product b context) where
  kernel := step.leftKernel context
  preserve := step.left_preserve context
  bad pair := step.bad (pair.1.1, pair.2.1)
  agree state reachable target next good := by
    have first : state.1 ∈ a.program.eval.support := by
      rw [← product_left a context, PMF.mem_support_map_iff]
      exact ⟨state, reachable, rfl⟩
    obtain ⟨y, hy, same⟩ := (PMF.mem_support_map_iff _ _ _).mp next
    subst target
    exact and_congr (step.agree state.1 first y hy good) Iff.rfl
  loss := step.loss
  bound := by
    have project := step.left_joint_project context
    have prob := eventProb_map
      ((product a context).program.eval.bind (fun x =>
        (step.leftKernel context x).map (fun y => (x, y))))
      (fun pair => (pair.1.1, pair.2.1)) step.bad
    rw [project] at prob
    exact prob.symm.trans_le step.bound

end Step

namespace Path

def left : {a b : Observed.{u}} → Path a b → (context : Observed.{u}) →
    Path (product a context) (product b context)
  | _, _, .identity a, context => .identity (product a context)
  | _, _, .step transition, context => .step (transition.left context)
  | _, _, .seq p q, context => .seq (p.left context) (q.left context)

theorem left_kernel {a b : Observed.{u}} (path : Path a b) (context : Observed.{u})
    (state : (product a context).Outcome) :
    (path.left context).kernel state = (path.kernel state.1).map (fun y => (y, state.2)) := by
  induction path with
  | identity =>
      rcases state with ⟨x, c⟩
      simp only [left, kernel, PMF.pure_map]
  | step => rfl
  | seq p q ihp ihq =>
      simp only [left, kernel, ihp, PMF.bind_map, Function.comp_def, PMF.map_bind]
      congr 1
      funext y
      exact ihq (y, state.2)

theorem left_loss {a b : Observed.{u}} (path : Path a b) (context : Observed.{u}) :
    (path.left context).loss = path.loss := by
  induction path with
  | identity => rfl
  | step => rfl
  | seq p q ihp ihq => exact congrArg₂ (· + ·) ihp ihq

def right {a b : Observed.{u}} (context : Observed.{u}) (path : Path a b) :
    Path (product context a) (product context b) :=
  .seq (.step (Step.swap context a))
    (.seq (path.left context) (.step (Step.swap b context)))

theorem right_kernel {a b : Observed.{u}} (context : Observed.{u}) (path : Path a b)
    (state : (product context a).Outcome) :
    (path.right context).kernel state = (path.kernel state.2).map (fun y => (state.1, y)) := by
  simp only [right, kernel, Step.swap, Step.ofMap, PMF.pure_bind, left_kernel,
    PMF.bind_map, Function.comp_def]
  rfl

theorem right_loss {a b : Observed.{u}} (context : Observed.{u}) (path : Path a b) :
    (path.right context).loss = path.loss := by
  simp only [right, loss, Step.swap, Step.ofMap, left_loss, add_zero, zero_add]

def parallel {a b c d : Observed.{u}} (p : Path a b) (q : Path c d) :
    Path (product a c) (product b d) := .seq (p.left c) (q.right b)

theorem parallel_kernel {a b c d : Observed.{u}} (p : Path a b) (q : Path c d)
    (state : (product a c).Outcome) :
    (p.parallel q).kernel state = (p.kernel state.1).bind
      (fun x => (q.kernel state.2).map (fun y => (x, y))) := by
  simp only [parallel, kernel, left_kernel, right_kernel, PMF.bind_map, Function.comp_def]

theorem parallel_loss {a b c d : Observed.{u}} (p : Path a b) (q : Path c d) :
    (p.parallel q).loss = p.loss + q.loss := by
  simp only [parallel, loss, left_loss, right_loss]

end Path

namespace Cell4

/-- This is probabilistic interchange on full state kernels. It applies to
positive-loss coupling steps too, without resampling shared state registers. -/
def exchange {a b c d : Observed.{u}} (p : Path a b) (q : Path c d) :
    Cell4 (.seq (p.left c) (q.right b)) (.seq (q.right a) (p.left d)) :=
  .generator ⟨by
    intro state
    simp only [Path.kernel, Path.left_kernel, Path.right_kernel, PMF.bind_map, Function.comp_def]
    exact PMF.bind_comm _ _ _, by
    simp only [Path.loss, Path.left_loss, Path.right_loss]
    exact add_comm _ _⟩

def left {a b : Observed.{u}} {p q : Path a b} (cell : Cell4 p q) (context : Observed.{u}) :
    Cell4 (p.left context) (q.left context) :=
  .generator ⟨by
    intro state
    simp only [Path.left_kernel]
    rw [cell.sound.kernel_eq], by
    simpa only [Path.left_loss] using cell.sound.loss_eq⟩

def right {a b : Observed.{u}} {p q : Path a b} (context : Observed.{u}) (cell : Cell4 p q) :
    Cell4 (p.right context) (q.right context) :=
  .generator ⟨by
    intro state
    simp only [Path.right_kernel]
    rw [cell.sound.kernel_eq], by
    simpa only [Path.right_loss] using cell.sound.loss_eq⟩

def parallel {a b c d : Observed.{u}} {p p' : Path a b} {q q' : Path c d}
    (first : Cell4 p p') (second : Cell4 q q') : Cell4 (p.parallel q) (p'.parallel q') :=
  .seq (first.left c) (second.right b)

end Cell4
end
end CryptoLogic.Polygraph.Experiment.GameCoherence
