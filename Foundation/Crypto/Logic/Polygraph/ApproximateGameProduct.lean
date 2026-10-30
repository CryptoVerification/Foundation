import Foundation.Crypto.Logic.Polygraph.ApproximateDiagramEdits
import Foundation.Crypto.Semantics.Probability.FiniteKernelFrames

/-! Independent product contexts and parallel composition for approximate
four-cells and annotated diagram edits. Each source is sampled once.
This product does not interpret copying a sampled state as resampling it. -/
namespace CryptoLogic.Polygraph.Experiment
open Foundation.Probability
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance productFintype (a b : Observed) [Fintype a.Outcome] [Fintype b.Outcome] :
    Fintype (product a b).Outcome := inferInstanceAs (Fintype (a.Outcome × b.Outcome))

theorem left_discrepancy {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    (p q : GameCoherence.Path a b) (context : Observed) [Fintype context.Outcome] :
    FiniteKernelVariation.distance (product a context).program.eval
      (p.left context).kernel (q.left context).kernel =
      FiniteKernelVariation.distance a.program.eval p.kernel q.kernel := by
  change FiniteKernelVariation.distance _
    (fun s => (p.left context).kernel s) (fun s => (q.left context).kernel s) = _
  simp_rw [Path.left_kernel]
  have h := FiniteKernelVariation.frame_eq
    (product a context).program.eval Prod.fst Prod.snd p.kernel q.kernel
  rw [product_left] at h
  exact h

namespace ApproximateGameCoherence.Cell4

def left {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    {p q : GameCoherence.Path a b} {δ} (cell : Cell4 p q δ)
    (context : Observed) [Fintype context.Outcome] : Cell4 (p.left context) (q.left context) δ := by
  apply Cell4.generator
  constructor
  · change FiniteKernelVariation.distance _
      (fun s => (p.left context).kernel s) (fun s => (q.left context).kernel s) ≤ δ
    simp_rw [Path.left_kernel]
    have h := FiniteKernelVariation.frame (product a context).program.eval
      Prod.fst Prod.snd p.kernel q.kernel
    rw [product_left] at h
    exact h.trans cell.sound.kernel_bound
  · simpa only [Path.left_loss] using cell.sound.loss_eq

def right {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    (context : Observed) [Fintype context.Outcome]
    {p q : GameCoherence.Path a b} {δ} (cell : Cell4 p q δ) :
    Cell4 (p.right context) (q.right context) δ := by
  apply Cell4.generator
  constructor
  · change FiniteKernelVariation.distance _
      (fun s => (p.right context).kernel s) (fun s => (q.right context).kernel s) ≤ δ
    simp_rw [Path.right_kernel]
    have h := FiniteKernelVariation.mapped (product context a).program.eval
      Prod.snd (fun s y => (s.1, y)) p.kernel q.kernel
    rw [product_right] at h
    exact h.trans cell.sound.kernel_bound
  · simpa only [Path.right_loss] using cell.sound.loss_eq

def parallel {a b c d : Observed}
    [Fintype a.Outcome] [Fintype b.Outcome] [Fintype c.Outcome] [Fintype d.Outcome]
    {p p' : GameCoherence.Path a b} {q q' : GameCoherence.Path c d} {δ ε}
    (first : Cell4 p p' δ) (second : Cell4 q q' ε) :
    Cell4 (p.parallel q) (p'.parallel q') (δ + ε) :=
  .seq (first.left c) (second.right b)

/-- Independent transformations can be executed in either order, even when
local game loss is positive. This introduces no additional comparison error. -/
def exchange {a b c d : Observed}
    [Fintype a.Outcome] [Fintype b.Outcome] [Fintype c.Outcome] [Fintype d.Outcome]
    (p : GameCoherence.Path a b) (q : GameCoherence.Path c d) :
    Cell4 (.seq (p.left c) (q.right b)) (.seq (q.right a) (p.left d)) 0 :=
  .exact (GameCoherence.Cell4.exchange p q)

end ApproximateGameCoherence.Cell4

namespace ApproximateDiagramEdits.Edit
open GameCoherence.DiagramBridge

def left {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    {d e : Closed a b} {δ} (edit : Edit d e δ)
    (context : Observed) [Fintype context.Outcome] :
    Edit (diagram ((evaluate d).left context)) (diagram ((evaluate e).left context)) δ := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact edit.comparison.left context

def right {a b : Observed} [Fintype a.Outcome] [Fintype b.Outcome]
    (context : Observed) [Fintype context.Outcome]
    {d e : Closed a b} {δ} (edit : Edit d e δ) :
    Edit (diagram ((evaluate d).right context)) (diagram ((evaluate e).right context)) δ := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact edit.comparison.right context

def parallel {a b c d : Observed}
    [Fintype a.Outcome] [Fintype b.Outcome] [Fintype c.Outcome] [Fintype d.Outcome]
    {first first' : Closed a b} {second second' : Closed c d} {δ ε}
    (leftEdit : Edit first first' δ) (rightEdit : Edit second second' ε) :
    Edit (diagram ((evaluate first).parallel (evaluate second)))
      (diagram ((evaluate first').parallel (evaluate second'))) (δ + ε) := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact leftEdit.comparison.parallel rightEdit.comparison

end ApproximateDiagramEdits.Edit
end
end CryptoLogic.Polygraph.Experiment
