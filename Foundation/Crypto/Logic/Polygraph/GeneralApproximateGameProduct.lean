import Foundation.Crypto.Logic.Polygraph.GeneralApproximateDiagramEdits
import Foundation.Crypto.Semantics.Probability.GeneralKernelFrames

/-! Independent product contexts, parallel composition and exact exchange
for approximate cells on arbitrary discrete outcome types. A retained value
is kept from the initial sample, without resampling its register. -/
namespace CryptoLogic.Polygraph.Experiment
open Foundation.Probability
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem general_left_discrepancy {a b : Observed}
    (p q : GameCoherence.Path a b) (context : Observed)  :
    GeneralKernelVariation.distance (product a context).program.eval
      (p.left context).kernel (q.left context).kernel =
      GeneralKernelVariation.distance a.program.eval p.kernel q.kernel := by
  change GeneralKernelVariation.distance _
    (fun s => (p.left context).kernel s) (fun s => (q.left context).kernel s) = _
  simp_rw [Path.left_kernel]
  have h := GeneralKernelVariation.frame_eq
    (product a context).program.eval Prod.fst Prod.snd p.kernel q.kernel
  rw [product_left] at h
  exact h

theorem general_right_discrepancy {a b : Observed}
    (p q : GameCoherence.Path a b) (context : Observed) :
    GeneralKernelVariation.distance (product context a).program.eval
      (p.right context).kernel (q.right context).kernel =
      GeneralKernelVariation.distance a.program.eval p.kernel q.kernel := by
  change GeneralKernelVariation.distance _
    (fun s => (p.right context).kernel s) (fun s => (q.right context).kernel s) = _
  simp_rw [Path.right_kernel]
  have h := GeneralKernelVariation.mapped_eq (product context a).program.eval
    Prod.snd (fun s y => (s.1,y)) (fun _ => Prod.snd) p.kernel q.kernel (fun _ _ => rfl)
  rw [product_right] at h
  exact h

namespace GeneralApproximateGameCoherence.Cell4

def left {a b : Observed}
    {p q : GameCoherence.Path a b} {δ} (cell : Cell4 p q δ)
    (context : Observed)  : Cell4 (p.left context) (q.left context) δ := by
  apply Cell4.generator
  constructor
  · change GeneralKernelVariation.distance _
      (fun s => (p.left context).kernel s) (fun s => (q.left context).kernel s) ≤ δ
    simp_rw [Path.left_kernel]
    have h := GeneralKernelVariation.frame (product a context).program.eval
      Prod.fst Prod.snd p.kernel q.kernel
    rw [product_left] at h
    exact h.trans cell.sound.kernel_bound
  · simpa only [Path.left_loss] using cell.sound.loss_eq

def right {a b : Observed}
    (context : Observed)
    {p q : GameCoherence.Path a b} {δ} (cell : Cell4 p q δ) :
    Cell4 (p.right context) (q.right context) δ := by
  apply Cell4.generator
  constructor
  · change GeneralKernelVariation.distance _
      (fun s => (p.right context).kernel s) (fun s => (q.right context).kernel s) ≤ δ
    simp_rw [Path.right_kernel]
    have h := GeneralKernelVariation.mapped (product context a).program.eval
      Prod.snd (fun s y => (s.1, y)) p.kernel q.kernel
    rw [product_right] at h
    exact h.trans cell.sound.kernel_bound
  · simpa only [Path.right_loss] using cell.sound.loss_eq

def parallel {a b c d : Observed}

    {p p' : GameCoherence.Path a b} {q q' : GameCoherence.Path c d} {δ ε}
    (first : Cell4 p p' δ) (second : Cell4 q q' ε) :
    Cell4 (p.parallel q) (p'.parallel q') (δ + ε) :=
  .seq (first.left c) (second.right b)

/-- Independent transformations can be executed in either order, even when
local game loss is positive. This introduces no additional comparison error. -/
def exchange {a b c d : Observed}

    (p : GameCoherence.Path a b) (q : GameCoherence.Path c d) :
    Cell4 (.seq (p.left c) (q.right b)) (.seq (q.right a) (p.left d)) 0 :=
  .exact (GameCoherence.Cell4.exchange p q)

end GeneralApproximateGameCoherence.Cell4

namespace GeneralApproximateDiagramEdits.Edit
open GameCoherence.DiagramBridge

def left {a b : Observed}
    {d e : Closed a b} {δ} (edit : Edit d e δ)
    (context : Observed)  :
    Edit (diagram ((evaluate d).left context)) (diagram ((evaluate e).left context)) δ := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact edit.comparison.left context

def right {a b : Observed}
    (context : Observed)
    {d e : Closed a b} {δ} (edit : Edit d e δ) :
    Edit (diagram ((evaluate d).right context)) (diagram ((evaluate e).right context)) δ := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact edit.comparison.right context

def parallel {a b c d : Observed}

    {first first' : Closed a b} {second second' : Closed c d} {δ ε}
    (leftEdit : Edit first first' δ) (rightEdit : Edit second second' ε) :
    Edit (diagram ((evaluate first).parallel (evaluate second)))
      (diagram ((evaluate first').parallel (evaluate second'))) (δ + ε) := by
  apply Edit.game
  simp only [evaluate_diagram]
  exact leftEdit.comparison.parallel rightEdit.comparison

end GeneralApproximateDiagramEdits.Edit
end
end CryptoLogic.Polygraph.Experiment
