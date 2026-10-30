import Foundation.Crypto.Logic.Polygraph.GameCoherence
import Foundation.Crypto.Semantics.Probability.GeneralVariationObservers
import Foundation.Crypto.Logic.Polygraph.ApproximateGameCoherence

/-! Proof-relevant approximate four-cells with arbitrary discrete endpoint
state types. Extended nonnegative kernel budgets compose by addition, and
allocated game-path losses remain equal. These are semantic certificates;
no machine execution or necessity claim is inferred from the state type. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence
open Foundation.Probability
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Comparison {left right : Observed}
    (p q : GameCoherence.Path left right) (δ : ℝ≥0∞) : Prop where
  kernel_bound : GeneralKernelVariation.distance left.program.eval p.kernel q.kernel ≤ δ
  loss_eq : p.loss = q.loss

namespace Comparison

theorem ofExact {left right : Observed}
    {p q : GameCoherence.Path left right} (h : GameCoherence.Comparison p q) : Comparison p q 0 := by
  constructor
  · have same : p.kernel = q.kernel := funext h.kernel_eq
    rw [same,GeneralKernelVariation.self]
  · exact h.loss_eq

end Comparison

inductive Cell4 : {left right : Observed} →
    GameCoherence.Path left right → GameCoherence.Path left right → ℝ≥0∞ → Type 1 where
  | generator {left right : Observed}
      {p q : GameCoherence.Path left right} {δ} : Comparison p q δ → Cell4 p q δ
  | exact {left right : Observed}
      {p q : GameCoherence.Path left right} : GameCoherence.Cell4 p q → Cell4 p q 0
  | refl {left right : Observed}
      (p : GameCoherence.Path left right) : Cell4 p p 0
  | symm {left right : Observed}
      {p q : GameCoherence.Path left right} {δ} : Cell4 p q δ → Cell4 q p δ
  | trans {left right : Observed}
      {p q r : GameCoherence.Path left right} {δ ε} : Cell4 p q δ → Cell4 q r ε → Cell4 p r (δ + ε)
  | weaken {left right : Observed}
      {p q : GameCoherence.Path left right} {δ ε} : Cell4 p q δ → δ ≤ ε → Cell4 p q ε
  | seq {left middle right : Observed}
      {p p' : GameCoherence.Path left middle} {q q' : GameCoherence.Path middle right} {δ ε} :
      Cell4 p p' δ → Cell4 q q' ε → Cell4 (.seq p q) (.seq p' q') (δ + ε)

namespace Cell4

theorem sound {left right : Observed}
    {p q : GameCoherence.Path left right} {δ : ℝ≥0∞} (cell : Cell4 p q δ) : Comparison p q δ := by
  induction cell with
  | generator h => exact h
  | exact h => exact Comparison.ofExact h.sound
  | refl p => exact ⟨by rw [GeneralKernelVariation.self],rfl⟩
  | symm h ih => exact ⟨by rw [GeneralKernelVariation.symm]; exact ih.kernel_bound,ih.loss_eq.symm⟩
  | trans h k ih ik =>
    exact ⟨(GeneralKernelVariation.triangle _ _ _ _).trans (add_le_add ih.kernel_bound ik.kernel_bound),
      ih.loss_eq.trans ik.loss_eq⟩
  | weaken h bound ih => exact ⟨ih.kernel_bound.trans bound,ih.loss_eq⟩
  | @seq left middle right p p' q q' δ ε h k ih ik =>
    constructor
    · exact (GeneralKernelVariation.seq left.program.eval middle.program.eval
        p.kernel p'.kernel q.kernel q'.kernel p'.preserve).trans (add_le_add ih.kernel_bound ik.kernel_bound)
    · exact congrArg₂ (· + ·) ih.loss_eq ik.loss_eq

def pre {before left right : Observed}
    (beforePath : GameCoherence.Path before left) {p q : GameCoherence.Path left right} {δ : ℝ≥0∞} (cell : Cell4 p q δ) :
    Cell4 (.seq beforePath p) (.seq beforePath q) δ :=
  by simpa only [zero_add] using Cell4.seq (Cell4.refl beforePath) cell

def post {left right after : Observed}
    {p q : GameCoherence.Path left right} {δ : ℝ≥0∞} (cell : Cell4 p q δ) (afterPath : GameCoherence.Path right after) :
    Cell4 (.seq p afterPath) (.seq q afterPath) δ :=
  by simpa only [add_zero] using Cell4.seq cell (Cell4.refl afterPath)

def contextual {before left right after : Observed}

    (beforePath : GameCoherence.Path before left) {p q : GameCoherence.Path left right} {δ : ℝ≥0∞} (cell : Cell4 p q δ)
    (afterPath : GameCoherence.Path right after) : Cell4 (.seq (.seq beforePath p) afterPath) (.seq (.seq beforePath q) afterPath) δ :=
  (cell.pre beforePath).post afterPath

def strictOfZero {left right : Observed}
    {p q : GameCoherence.Path left right} (cell : Cell4 p q 0) (full : ∀ x, x ∈ left.program.eval.support) :
    GameCoherence.Cell4 p q := by
  apply GameCoherence.Cell4.generator
  constructor
  · have zero := le_antisymm cell.sound.kernel_bound bot_le
    exact fun x => GeneralKernelVariation.zero_on_support _ _ _ zero x (full x)
  · exact cell.sound.loss_eq

theorem joint_observer_bound {left right : Observed}
    {p q : GameCoherence.Path left right} {δ : ℝ≥0∞} (cell : Cell4 p q δ) {T : Type}
    (observer : left.Outcome × right.Outcome → PMF T) (event : T → Prop) :
    probabilityGap (eventProb (p.joint.bind observer) event) (eventProb (q.joint.bind observer) event) ≤ δ := by
  have bound := (GeneralKernelVariation.joint_observer_bound left.program.eval p.kernel q.kernel observer event).trans
    cell.sound.kernel_bound
  simpa only [GeneralKernelVariation.joint,GameCoherence.Path.joint] using bound

end Cell4

def ofFinite {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ}
    (cell : ApproximateGameCoherence.Cell4 p q δ) : Cell4 p q (ENNReal.ofReal δ) := by
  apply Cell4.generator
  constructor
  · rw [GeneralKernelVariation.distance_finite_eq]
    exact ENNReal.ofReal_le_ofReal cell.sound.kernel_bound
  · exact cell.sound.loss_eq

end
end CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence
