import Foundation.Crypto.Logic.Polygraph.GameCoherenceDiagram
import Foundation.Crypto.Logic.Polygraph.ApproximateDiagramEdits
import Foundation.Crypto.Logic.Polygraph.GeneralApproximateGameCoherence

/-! Error-annotated diagram edits for arbitrary discrete endpoint state
types. Structural and strict edits cost zero. Vertical and sequential pasting
add discrepancy; surrounding game contexts preserve it. No runtime is inferred. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits
open Foundation.Probability
open scoped ENNReal
open GameCoherence.DiagramBridge
set_option backward.isDefEq.respectTransparency false
noncomputable section

inductive Edit {a b : Observed}   :
    Closed a b → Closed a b → ℝ≥0∞ → Type 2 where
  | structural {d e} : Foundation.Logic.Polygraph.Diagram.Cell3 d e → Edit d e 0
  | strict {d e} : Edits d e → Edit d e 0
  | game {d e} {δ} : GeneralApproximateGameCoherence.Cell4 (evaluate d) (evaluate e) δ → Edit d e δ
  | refl (d) : Edit d d 0
  | symm {d e} {δ} : Edit d e δ → Edit e d δ
  | trans {d e f} {δ ε} : Edit d e δ → Edit e f ε → Edit d f (δ + ε)
  | weaken {d e} {δ ε} : Edit d e δ → δ ≤ ε → Edit d e ε

namespace Edit

def comparison {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ) :
    GeneralApproximateGameCoherence.Cell4 (evaluate d) (evaluate e) δ := by
  induction edit with
  | structural h => exact (GameCoherence.DiagramBridge.structural h) ▸ .refl _
  | strict h => exact .exact (edit_comparison h)
  | game h => exact h
  | refl d => exact .refl _
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | weaken h bound ih => exact .weaken ih bound

theorem kernel_bound {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ) :
    GeneralKernelVariation.distance a.program.eval (evaluate d).kernel (evaluate e).kernel ≤ δ :=
  edit.comparison.sound.kernel_bound

theorem loss_eq {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ) : (evaluate d).loss = (evaluate e).loss :=
  edit.comparison.sound.loss_eq

def contextual {before a b after : Observed}

    (beforePath : GameCoherence.Path before a) {d e : Closed a b} {δ} (edit : Edit d e δ)
    (afterPath : GameCoherence.Path b after) :
    Edit (diagram (.seq (.seq beforePath (evaluate d)) afterPath))
      (diagram (.seq (.seq beforePath (evaluate e)) afterPath)) δ := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact edit.comparison.contextual beforePath afterPath

def seq {a middle b : Observed}

    {d e : Closed a middle} {f g : Closed middle b} {δ ε}
    (first : Edit d e δ) (second : Edit f g ε) :
    Edit (diagram (.seq (evaluate d) (evaluate f)))
      (diagram (.seq (evaluate e) (evaluate g))) (δ + ε) := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact .seq first.comparison second.comparison

theorem observer_bound {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ) {T : Type}
    (observer : a.Outcome × b.Outcome → PMF T) (event : T → Prop) :
    probabilityGap (eventProb ((evaluate d).joint.bind observer) event)
      (eventProb ((evaluate e).joint.bind observer) event) ≤ δ :=
  edit.comparison.joint_observer_bound observer event

theorem game_bound {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ) :
    probabilityGap a.probability b.probability ≤ (evaluate d).loss ∧
    probabilityGap a.probability b.probability ≤ (evaluate e).loss :=
  ⟨(evaluate d).sound, edit.loss_eq ▸ (evaluate d).sound⟩

end Edit

def ofFinite {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    {d e : Closed a b} {δ : ℝ} (edit : ApproximateDiagramEdits.Edit d e δ) :
    Edit d e (ENNReal.ofReal δ) := .game (GeneralApproximateGameCoherence.ofFinite edit.comparison)

end
end CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits
