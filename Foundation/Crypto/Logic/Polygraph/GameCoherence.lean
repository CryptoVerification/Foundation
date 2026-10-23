import Foundation.Crypto.Logic.Polygraph.ExperimentSyntax

/-! Proof-relevant, directed probabilistic game transformations. A step
retains its conditional state kernel, not just its endpoint laws. Four-cells
compare these kernels and losses. Sampling and erasure are directed: symmetry
of a comparison never introduces an inverse stochastic state transformation.
All state/certificate data that must be preserved belong in the outcome type.
No coherence of arbitrary couplings is assumed from marginal equalities. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence

open Foundation.Probability
open scoped ENNReal
universe u v
set_option backward.isDefEq.respectTransparency false

theorem eval_map {A B : Type u} (program : Program A) (f : A → B) :
    (program.map f).eval = program.eval.map f := rfl

structure Step (left right : Observed.{u}) where
  kernel : left.Outcome → PMF right.Outcome
  preserve : left.program.eval.bind kernel = right.program.eval
  bad : left.Outcome × right.Outcome → Prop
  agree : ∀ x ∈ left.program.eval.support, ∀ y ∈ (kernel x).support,
    ¬bad (x, y) → (left.event x ↔ right.event y)
  loss : ℝ≥0∞
  bound : eventProb (left.program.eval.bind fun x => (kernel x).map (fun y => (x, y))) bad ≤ loss

namespace Step
variable {left right : Observed.{u}} (step : Step left right)

noncomputable def joint : PMF (left.Outcome × right.Outcome) :=
  left.program.eval.bind fun x => (step.kernel x).map fun y => (x, y)

theorem joint_left : step.joint.map Prod.fst = left.program.eval := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.program.eval.bind fun x => (step.kernel x).map
    (Function.const right.Outcome x)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem joint_right : step.joint.map Prod.snd = right.program.eval := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.program.eval.bind fun x => (step.kernel x).map id) = _
  simp only [PMF.map_id]
  exact step.preserve

noncomputable def hop : Hop left right step.loss :=
  (Hop.coupling step.joint Prod.fst Prod.snd step.joint_left step.joint_right step.bad (by
    intro pair reachable good
    obtain ⟨x, hx, reachable⟩ := (PMF.mem_support_bind_iff _ _ _).mp reachable
    obtain ⟨y, hy, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reachable
    subst pair
    exact step.agree x hx y hy good)).weaken step.bound

/-- Deterministic changes include copying a sampled value, forgetting a
private register, and changing a state representation. Each event must factor
through the supplied state map; this is not permission to rerun randomness. -/
noncomputable def ofMap (left right : Observed.{u}) (f : left.Outcome → right.Outcome)
    (preserve : left.program.eval.map f = right.program.eval)
    (agree : ∀ x ∈ left.program.eval.support, left.event x ↔ right.event (f x)) :
    Step left right where
  kernel x := PMF.pure (f x)
  preserve := preserve
  bad _ := False
  agree x hx y hy _ := by
    have same := (PMF.mem_support_pure_iff _ _).mp hy
    subst y
    exact agree x hx
  loss := 0
  bound := by simp [eventProb]

/-- Lift every existing exact program transformation, including independent
sampling exchange, bind reassociation and reindexing. The retained outcome
is unchanged. Internal random choices absent from that type are not claimed
to have a canonical identity correspondence. -/
noncomputable def exact {A : Type u} {p q : Program A} (path : ExactPath p q) (event : A → Prop) :
    Step ⟨A, p, event⟩ ⟨A, q, event⟩ :=
  ofMap _ _ id (by simpa only [PMF.map_id] using path.sound) (fun _ _ => Iff.rfl)

end Step

inductive Path : Observed.{u} → Observed.{u} → Type (u + 1) where
  | identity (game) : Path game game
  | step {left right} : Step left right → Path left right
  | seq {left middle right} : Path left middle → Path middle right → Path left right

namespace Path

noncomputable def kernel : {left right : Observed.{u}} → Path left right →
    left.Outcome → PMF right.Outcome
  | _, _, .identity _, x => PMF.pure x
  | _, _, .step transition, x => transition.kernel x
  | _, _, .seq p q, x => (p.kernel x).bind q.kernel

def loss : {left right : Observed.{u}} → Path left right → ℝ≥0∞
  | _, _, .identity _ => 0
  | _, _, .step transition => transition.loss
  | _, _, .seq p q => p.loss + q.loss

theorem preserve {left right : Observed.{u}} (path : Path left right) :
    left.program.eval.bind path.kernel = right.program.eval := by
  induction path with
  | identity => exact PMF.bind_pure _
  | step step => exact step.preserve
  | seq p q ihp ihq =>
      rw [← ihq, ← ihp, PMF.bind_bind]
      rfl

noncomputable def hop : {left right : Observed.{u}} → (path : Path left right) → Hop left right path.loss
  | _, _, .identity game => .exact (.refl _) game.event
  | _, _, .step transition => transition.hop
  | _, _, .seq p q => .comp p.hop q.hop

theorem sound {left right : Observed.{u}} (path : Path left right) :
    probabilityGap left.probability right.probability ≤ path.loss := path.hop.sound

/-- Retain the original input together with the final complete state. -/
noncomputable def joint {left right : Observed.{u}} (path : Path left right) :
    PMF (left.Outcome × right.Outcome) :=
  left.program.eval.bind fun x => (path.kernel x).map fun y => (x, y)

theorem joint_left {left right : Observed.{u}} (path : Path left right) :
    path.joint.map Prod.fst = left.program.eval := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.program.eval.bind fun x => (path.kernel x).map
    (Function.const right.Outcome x)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem joint_right {left right : Observed.{u}} (path : Path left right) :
    path.joint.map Prod.snd = right.program.eval := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.program.eval.bind fun x => (path.kernel x).map id) = _
  simp only [PMF.map_id]
  exact path.preserve

end Path

/-- A local four-dimensional comparison has two independently checked parts.
Kernel equality is pointwise, even before sampling the initial game law. -/
structure Comparison {left right : Observed.{u}} (p q : Path left right) : Prop where
  kernel_eq : ∀ x, p.kernel x = q.kernel x
  loss_eq : p.loss = q.loss

/-- Four-cells are data, closed under higher pasting and sequential contexts.
Only certified local comparisons are generators. Directed game paths have
no inverse constructor, including when a comparison itself is reversed. -/
inductive Cell4 : {left right : Observed.{u}} → Path left right → Path left right → Type (u + 1) where
  | generator {left right} {p q : Path left right} : Comparison p q → Cell4 p q
  | refl {left right} (p : Path left right) : Cell4 p p
  | symm {left right} {p q : Path left right} : Cell4 p q → Cell4 q p
  | trans {left right} {p q r : Path left right} : Cell4 p q → Cell4 q r → Cell4 p r
  | seq {left middle right} {p p' : Path left middle} {q q' : Path middle right} :
      Cell4 p p' → Cell4 q q' → Cell4 (.seq p q) (.seq p' q')
  | assoc {a b c d} (p : Path a b) (q : Path b c) (r : Path c d) :
      Cell4 (.seq (.seq p q) r) (.seq p (.seq q r))
  | leftUnit {left right} (p : Path left right) : Cell4 (.seq (.identity left) p) p
  | rightUnit {left right} (p : Path left right) : Cell4 (.seq p (.identity right)) p

namespace Cell4

theorem sound {left right : Observed.{u}} {p q : Path left right} (cell : Cell4 p q) : Comparison p q := by
  induction cell with
  | generator h => exact h
  | refl => exact ⟨fun _ => rfl, rfl⟩
  | symm h ih => exact ⟨fun x => (ih.kernel_eq x).symm, ih.loss_eq.symm⟩
  | trans h k ih ik => exact ⟨fun x => (ih.kernel_eq x).trans (ik.kernel_eq x), ih.loss_eq.trans ik.loss_eq⟩
  | seq h k ih ik =>
      constructor
      · intro x
        change (_ : PMF _).bind _ = _
        rw [ih.kernel_eq x]
        exact congrArg (PMF.bind _) (funext ik.kernel_eq)
      · exact congrArg₂ (· + ·) ih.loss_eq ik.loss_eq
  | assoc p q r => exact ⟨fun x => PMF.bind_bind _ _ _, add_assoc _ _ _⟩
  | leftUnit p => exact ⟨fun x => PMF.pure_bind _ _, zero_add _⟩
  | rightUnit p => exact ⟨fun x => PMF.bind_pure _, add_zero _⟩

theorem joint_eq {left right : Observed.{u}} {p q : Path left right} (cell : Cell4 p q) :
    p.joint = q.joint := by
  unfold Path.joint
  simp_rw [cell.sound.kernel_eq]

/-- Every retained observation, including code, resources, cache and random
reserve, has the same conditional law along related transformation paths. -/
theorem retained_law {left right : Observed.{u}} {p q : Path left right}
    (cell : Cell4 p q) {A : Type u} (observe : right.Outcome → A) (initial : left.Outcome) :
    (p.kernel initial).map observe = (q.kernel initial).map observe := by
  rw [cell.sound.kernel_eq]

/-- Deterministically extracted data are equal as values, not just equal in
probability or equal after forgetting their execution certificates. -/
theorem deterministic_output {left right : Observed.{u}} {p q : Path left right}
    (cell : Cell4 p q) {A : Type u} (observe : right.Outcome → A) (initial : left.Outcome)
    (first second : A)
    (hp : (p.kernel initial).map observe = PMF.pure first)
    (hq : (q.kernel initial).map observe = PMF.pure second) : first = second := by
  have same : PMF.pure first = PMF.pure second := hp.symm.trans ((cell.retained_law observe initial).trans hq)
  apply (PMF.mem_support_pure_iff second first).mp
  rw [← same]
  exact (PMF.mem_support_pure_iff first first).mpr rfl

end Cell4

end CryptoLogic.Polygraph.Experiment.GameCoherence
