import Foundation.Crypto.Logic.Polygraph.GameCoherenceProduct
import Foundation.Crypto.Logic.Polygraph.GameCoherenceCoupling
import Foundation.Logic.Polygraph.CartesianCoherence

/-! Connect the directed probabilistic interpretation to the existing raw
inference diagrams, including structural copying/erasure of proof certificates.
Probabilistic sampling is performed by game paths, not by copying a raw proof
node. Closed proof edits may mix old structural cells with new game four-cells. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.DiagramBridge
open Foundation.Logic Foundation.Logic.Polygraph
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.checkUnivs false
noncomputable section

structure Boundary where
  first : Observed
  last : Observed

inductive Rule where
  | identity (game : Observed)
  | transition {a b : Observed} (step : Step a b)
  | sequence (a b c : Observed)
  | parallel (a b c d : Observed)

abbrev theory : Foundation.Logic.Presentation where
  Judgment := Boundary
  Rule := Rule
  arity := fun | .identity .. | .transition .. => 0 | .sequence .. | .parallel .. => 2
  premise := fun
    | .identity .. | .transition .. => Fin.elim0
    | .sequence a b c => Fin.cases ⟨a, b⟩ (fun _ => ⟨b, c⟩)
    | .parallel a b c d => Fin.cases ⟨a, b⟩ (fun _ => ⟨c, d⟩)
  conclusion := fun
    | .identity game => ⟨game, game⟩
    | .transition (a := a) (b := b) _ => ⟨a, b⟩
    | .sequence a _ c => ⟨a, c⟩
    | .parallel a b c d => ⟨product a c, product b d⟩

def interpretation : Foundation.Logic.Model theory where
  Carrier boundary := Path boundary.first boundary.last
  operation rule premises := match rule with
    | .identity game => .identity game
    | .transition transition => .step transition
    | .sequence .. => .seq (premises 0) (premises 1)
    | .parallel .. => (premises 0).parallel (premises 1)

def derivation : {a b : Observed} → Path a b →
    Foundation.Logic.Derivation theory (Context.empty theory) ⟨a, b⟩
  | _, _, .identity game => .apply (T := theory) (Rule.identity game) (fun i => Fin.elim0 i)
  | _, _, .step transition => .apply (T := theory) (Rule.transition transition) (fun i => Fin.elim0 i)
  | a, b, .seq (middle := middle) p q =>
      .apply (T := theory) (Rule.sequence a middle b) (Fin.cases (derivation p) (fun _ => derivation q))

theorem derivation_eval {a b : Observed} (path : Path a b) :
    (derivation path).eval interpretation (fun i => Fin.elim0 i) = path := by
  induction path with
  | identity => rfl
  | step => rfl
  | seq p q ihp ihq =>
      change Path.seq ((derivation p).eval interpretation _) ((derivation q).eval interpretation _) = _
      exact congrArg₂ Path.seq ihp ihq

abbrev Closed (a b : Observed) :=
  Diagram theory (Context.empty theory) (Context.singleton (⟨a, b⟩ : Boundary))

def diagram {a b : Observed} (path : Path a b) : Closed a b := Diagram.ofDerivation (derivation path)

def evaluate {a b : Observed} (proof : Closed a b) : Path a b :=
  proof.eval interpretation (fun i => Fin.elim0 i) 0

theorem evaluate_diagram {a b : Observed} (path : Path a b) : evaluate (diagram path) = path := by
  unfold evaluate diagram
  rw [Diagram.eval_ofDerivation]
  exact derivation_eval path

theorem structural {a b : Observed} {d e : Closed a b} (path : Diagram.Cell3 d e) :
    evaluate d = evaluate e := by
  exact congrFun (path.eval_eq interpretation (fun i => Fin.elim0 i)) 0

/-- A proof edit changes a derivation, not the stochastic state itself.
Reversing an edit is therefore allowed without reversing sampling or erasure. -/
inductive Edit {a b : Observed} : Closed a b → Closed a b → Type 2 where
  | structural {d e} : Diagram.Cell3 d e → Edit d e
  | game {d e} : Cell4 (evaluate d) (evaluate e) → Edit d e

abbrev Edits {a b : Observed} (d e : Closed a b) := Track (@Edit a b) d e

def edit_comparison {a b : Observed} {d e : Closed a b} :
    Edits d e → Cell4 (evaluate d) (evaluate e)
  | .refl _ => .refl _
  | .step (.structural path) => structural path ▸ Cell4.refl _
  | .step (.game cell) => cell
  | .comp p q => .trans (edit_comparison p) (edit_comparison q)
  | .inv p => .symm (edit_comparison p)

theorem edited_kernel {a b : Observed} {d e : Closed a b} (edits : Edits d e) (state : a.Outcome) :
    (evaluate d).kernel state = (evaluate e).kernel state := (edit_comparison edits).sound.kernel_eq state

theorem edited_loss {a b : Observed} {d e : Closed a b} (edits : Edits d e) :
    (evaluate d).loss = (evaluate e).loss := (edit_comparison edits).sound.loss_eq

theorem edited_joint {a b : Observed} {d e : Closed a b} (edits : Edits d e) :
    (evaluate d).joint = (evaluate e).joint := (edit_comparison edits).joint_eq

theorem edited_bound {a b : Observed} {d e : Closed a b} (edits : Edits d e) :
    probabilityGap a.probability b.probability ≤ (evaluate d).loss ∧
    probabilityGap a.probability b.probability ≤ (evaluate e).loss :=
  ⟨(evaluate d).sound, (edited_loss edits) ▸ (evaluate d).sound⟩

/-- The same accumulated loss bounds disagreement in the retained original /
final state coupling, before and after any certified mixed proof edits. -/
theorem edited_mismatch_bound {a b : Observed} {d e : Closed a b} (edits : Edits d e) :
    eventProb (evaluate d).joint (mismatch a b) ≤ (evaluate d).loss ∧
    eventProb (evaluate e).joint (mismatch a b) ≤ (evaluate d).loss := by
  exact ⟨(evaluate d).mismatch_bound,
    (edited_joint edits) ▸ (evaluate d).mismatch_bound⟩

end
end CryptoLogic.Polygraph.Experiment.GameCoherence.DiagramBridge
