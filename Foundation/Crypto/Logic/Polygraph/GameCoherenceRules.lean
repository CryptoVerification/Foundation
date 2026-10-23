import Foundation.Crypto.Logic.Polygraph.GameCoherenceProduct

/-! Certified probabilistic generators: fresh private sampling, deterministic
copying, and erasure. Their local four-cells are proved on conditional kernels.
Copying a sampled value is distinct from evaluating a computation twice. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence
open Foundation.Probability
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

def privateGame {A : Type u} (law : PMF A) : Observed.{u} := ⟨A, .sample law, fun _ => True⟩

def sample (game : Observed.{u}) {A : Type u} (law : PMF A) : Step game (product game (privateGame law)) where
  kernel x := law.map (fun value => (x, value))
  preserve := rfl
  bad _ := False
  agree x _ pair reachable _ := by
    obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reachable
    subst pair
    simp only [product, privateGame, and_true]
  loss := 0
  bound := by simp [eventProb]

def eraseSample (game : Observed.{u}) {A : Type u} (law : PMF A) :
    Step (product game (privateGame law)) game :=
  Step.ofMap _ _ Prod.fst (product_left _ _) (fun _ _ => by simp only [product, privateGame, and_true])

def sampleErase (game : Observed.{u}) {A : Type u} (law : PMF A) :
    Cell4 (.seq (.step (sample game law)) (.step (eraseSample game law))) (.identity game) :=
  .generator ⟨by
    intro x
    simp only [Path.kernel, sample, eraseSample, Step.ofMap, PMF.bind_map, Function.comp_def]
    change law.map (Function.const A x) = PMF.pure x
    exact PMF.map_const _ _, by simp only [Path.loss, sample, eraseSample, Step.ofMap, add_zero]⟩

def copyGame (game : Observed.{u}) : Observed.{u} where
  Outcome := game.Outcome × game.Outcome
  program := game.program.map (fun x => (x, x))
  event pair := game.event pair.1

def copy (game : Observed.{u}) : Step game (copyGame game) :=
  Step.ofMap _ _ (fun x => (x, x)) rfl (fun _ _ => Iff.rfl)

def eraseCopy (game : Observed.{u}) : Step (copyGame game) game :=
  Step.ofMap _ _ Prod.fst (by
    change (game.program.eval.map (fun x => (x, x))).map Prod.fst = _
    rw [PMF.map_comp]
    exact PMF.map_id _) (fun _ _ => Iff.rfl)

def copyErase (game : Observed.{u}) :
    Cell4 (.seq (.step (copy game)) (.step (eraseCopy game))) (.identity game) :=
  .generator ⟨by
    intro x
    simp only [Path.kernel, copy, eraseCopy, Step.ofMap, PMF.pure_bind], by
    simp only [Path.loss, copy, eraseCopy, Step.ofMap, add_zero]⟩

/-- All existing exact game rewrite paths choose the identity correspondence
on their explicitly retained common outcome type. This is a declared coupling
choice, not reconstruction of omitted internal random tapes. -/
def exactRoutes {A : Type u} {p q : Program A} (first second : ExactPath p q) (event : A → Prop) :
    Cell4 (.step (Step.exact first event)) (.step (Step.exact second event)) :=
  .generator ⟨fun _ => rfl, rfl⟩

end
end CryptoLogic.Polygraph.Experiment.GameCoherence
