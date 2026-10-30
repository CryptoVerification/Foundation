import Foundation.Crypto.Logic.Polygraph.CorrelatedGameFrames
import Foundation.Crypto.Logic.Polygraph.GeneralApproximateGameProduct

/-! Approximate transport along correlated frames on arbitrary state types.
Whole-joint preservation remains explicit. Local equality of conditional side
information constructs that preservation without assuming independence. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames
open Foundation.Probability GameCoherence CorrelatedGameFrames
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem lift_distance {a b : Observed} {C : Type}
    (source : Frame a C) (target : Frame b C) (test : C → Prop) (p q : GameCoherence.Path a b)
    (hp : Compatible source target p) (hq : Compatible source target q) :
    GeneralKernelVariation.distance (source.observed test).program.eval
      (lift source target test p hp).kernel (lift source target test q hq).kernel =
      GeneralKernelVariation.distance a.program.eval p.kernel q.kernel := by
  change GeneralKernelVariation.distance source.law (framedKernel p) (framedKernel q) = _
  have h := GeneralKernelVariation.frame_eq source.law Prod.fst Prod.snd p.kernel q.kernel
  rw [source.marginal] at h
  exact h

def liftCell {a b : Observed} {C : Type}
    (source : Frame a C) (target : Frame b C) (test : C → Prop)
    {p q : GameCoherence.Path a b} {δ} (cell : GeneralApproximateGameCoherence.Cell4 p q δ)
    (hp : Compatible source target p) (hq : Compatible source target q) :
    GeneralApproximateGameCoherence.Cell4 (lift source target test p hp) (lift source target test q hq) δ :=
  .generator ⟨by rw [lift_distance]; exact cell.sound.kernel_bound, cell.sound.loss_eq⟩

def liftEdit {a b : Observed} {C : Type}
    (source : Frame a C) (target : Frame b C) (test : C → Prop)
    {d e : GameCoherence.DiagramBridge.Closed a b} {δ}
    (edit : GeneralApproximateDiagramEdits.Edit d e δ)
    (hp : Compatible source target (GameCoherence.DiagramBridge.evaluate d))
    (hq : Compatible source target (GameCoherence.DiagramBridge.evaluate e)) :
    GeneralApproximateDiagramEdits.Edit
      (GameCoherence.DiagramBridge.diagram
        (lift source target test (GameCoherence.DiagramBridge.evaluate d) hp))
      (GameCoherence.DiagramBridge.diagram
        (lift source target test (GameCoherence.DiagramBridge.evaluate e) hq)) δ := by
  apply GeneralApproximateDiagramEdits.Edit.game
  simp only [GameCoherence.DiagramBridge.evaluate_diagram]
  exact liftCell source target test edit.comparison hp hq

def liftSeq {a b c : Observed} {C : Type}
    (source : Frame a C) (middle : Frame b C) (target : Frame c C) (test : C → Prop)
    (p : GameCoherence.Path a b) (q : GameCoherence.Path b c)
    (hp : Compatible source middle p) (hq : Compatible middle target q) :
    GeneralApproximateGameCoherence.Cell4
      (lift source target test (.seq p q) (compatible_seq source middle target p q hp hq))
      (.seq (lift source middle test p hp) (lift middle target test q hq)) 0 :=
  .exact (CorrelatedGameFrames.liftSeq source middle target test p q hp hq)

def stochasticTagged (game : Observed) {C : Type} (tag : game.Outcome → PMF C) : Frame game C where
  law := game.program.eval.bind (fun x => (tag x).map (fun c => (x,c)))
  marginal := by
    simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
    change game.program.eval.bind (fun x => (tag x).map (Function.const C x)) = _
    simp only [PMF.map_const,PMF.bind_pure]

theorem compatible_stochasticTagged {a b : Observed} {C : Type}
    (sourceTag : a.Outcome → PMF C) (targetTag : b.Outcome → PMF C) (path : GameCoherence.Path a b)
    (invariant : ∀ x ∈ a.program.eval.support, ∀ y ∈ (path.kernel x).support, targetTag y = sourceTag x) :
    Compatible (stochasticTagged a sourceTag) (stochasticTagged b targetTag) path := by
  unfold Compatible stochasticTagged framedKernel
  simp only [PMF.bind_bind,PMF.bind_map,Function.comp_def]
  rw [← path.preserve,PMF.bind_bind]
  apply bind_congr_of_support
  intro x supported
  change (sourceTag x).bind (fun c => (path.kernel x).bind (fun y => PMF.pure (y,c))) = _
  rw [PMF.bind_comm]
  apply bind_congr_of_support
  intro y reached
  rw [invariant x supported y reached]
  rfl

end
end CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames
