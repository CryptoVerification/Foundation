import Foundation.Crypto.Logic.Polygraph.GameCoherence
import Foundation.Crypto.Semantics.Probability.FiniteKernelVariation

/-! Proof-relevant approximate four-cells for finite endpoint outcomes.
The kernel discrepancy is averaged over the initial game law; allocated
game-path losses remain equal. Pasting adds discrepancies, and a common
preserving sequential context contracts them. No native runtime is assigned. -/
namespace CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence
open Foundation.Probability
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Comparison {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    (p q : GameCoherence.Path left right) (δ : ℝ) : Prop where
  kernel_bound : FiniteKernelVariation.distance left.program.eval p.kernel q.kernel ≤ δ
  loss_eq : p.loss = q.loss

namespace Comparison

theorem ofExact {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} (h : GameCoherence.Comparison p q) : Comparison p q 0 := by
  constructor
  · have same : p.kernel = q.kernel := funext h.kernel_eq
    rw [same,FiniteKernelVariation.self]
  · exact h.loss_eq

end Comparison

inductive Cell4 : {left right : Observed} → [Fintype left.Outcome] → [Fintype right.Outcome] →
    GameCoherence.Path left right → GameCoherence.Path left right → ℝ → Type 1 where
  | generator {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      {p q : GameCoherence.Path left right} {δ} : Comparison p q δ → Cell4 p q δ
  | exact {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      {p q : GameCoherence.Path left right} : GameCoherence.Cell4 p q → Cell4 p q 0
  | refl {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      (p : GameCoherence.Path left right) : Cell4 p p 0
  | symm {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      {p q : GameCoherence.Path left right} {δ} : Cell4 p q δ → Cell4 q p δ
  | trans {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      {p q r : GameCoherence.Path left right} {δ ε} : Cell4 p q δ → Cell4 q r ε → Cell4 p r (δ + ε)
  | weaken {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
      {p q : GameCoherence.Path left right} {δ ε} : Cell4 p q δ → δ ≤ ε → Cell4 p q ε
  | seq {left middle right : Observed} [Fintype left.Outcome] [Fintype middle.Outcome] [Fintype right.Outcome]
      {p p' : GameCoherence.Path left middle} {q q' : GameCoherence.Path middle right} {δ ε} :
      Cell4 p p' δ → Cell4 q q' ε → Cell4 (.seq p q) (.seq p' q') (δ + ε)

namespace Cell4

theorem sound {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) : Comparison p q δ := by
  induction cell with
  | generator h => exact h
  | exact h => exact Comparison.ofExact h.sound
  | refl p => exact ⟨by rw [FiniteKernelVariation.self],rfl⟩
  | symm h ih => exact ⟨by rw [FiniteKernelVariation.symm]; exact ih.kernel_bound,ih.loss_eq.symm⟩
  | trans h k ih ik =>
    exact ⟨(FiniteKernelVariation.triangle _ _ _ _).trans (add_le_add ih.kernel_bound ik.kernel_bound),
      ih.loss_eq.trans ik.loss_eq⟩
  | weaken h bound ih => exact ⟨ih.kernel_bound.trans bound,ih.loss_eq⟩
  | @seq left middle right _ _ _ p p' q q' δ ε h k ih ik =>
    constructor
    · exact (FiniteKernelVariation.seq left.program.eval middle.program.eval
        p.kernel p'.kernel q.kernel q'.kernel p'.preserve).trans (add_le_add ih.kernel_bound ik.kernel_bound)
    · exact congrArg₂ (· + ·) ih.loss_eq ik.loss_eq

theorem nonneg {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) : 0 ≤ δ :=
  (FiniteKernelVariation.nonneg _ _ _).trans cell.sound.kernel_bound

def pre {before left right : Observed} [Fintype before.Outcome] [Fintype left.Outcome] [Fintype right.Outcome]
    (beforePath : GameCoherence.Path before left) {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) :
    Cell4 (.seq beforePath p) (.seq beforePath q) δ :=
  by simpa only [zero_add] using Cell4.seq (Cell4.refl beforePath) cell

def post {left right after : Observed} [Fintype left.Outcome] [Fintype right.Outcome] [Fintype after.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) (afterPath : GameCoherence.Path right after) :
    Cell4 (.seq p afterPath) (.seq q afterPath) δ :=
  by simpa only [add_zero] using Cell4.seq cell (Cell4.refl afterPath)

def contextual {before left right after : Observed}
    [Fintype before.Outcome] [Fintype left.Outcome] [Fintype right.Outcome] [Fintype after.Outcome]
    (beforePath : GameCoherence.Path before left) {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ)
    (afterPath : GameCoherence.Path right after) : Cell4 (.seq (.seq beforePath p) afterPath) (.seq (.seq beforePath q) afterPath) δ :=
  (cell.pre beforePath).post afterPath

def strictOfZero {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} (cell : Cell4 p q 0) (full : ∀ x, x ∈ left.program.eval.support) :
    GameCoherence.Cell4 p q := by
  apply GameCoherence.Cell4.generator
  constructor
  · have zero := le_antisymm cell.sound.kernel_bound (FiniteKernelVariation.nonneg _ _ _)
    exact fun x => FiniteKernelVariation.zero_on_support _ _ _ zero x (full x)
  · exact cell.sound.loss_eq

theorem retained_observer_bound {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) {T : Type}
    (observer : left.Outcome → right.Outcome → PMF T) (event : T → Prop) :
    (∑ x, (left.program.eval x).toReal *
      |(eventProb ((p.kernel x).bind (observer x)) event).toReal -
        (eventProb ((q.kernel x).bind (observer x)) event).toReal|) ≤ δ := by
  apply le_trans _ cell.sound.kernel_bound
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (probabilistic_event_real_bound _ _ _ event) ENNReal.toReal_nonneg)

theorem joint_observer_bound {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) {T : Type}
    (observer : left.Outcome × right.Outcome → PMF T) (event : T → Prop) :
    |(eventProb (p.joint.bind observer) event).toReal -
      (eventProb (q.joint.bind observer) event).toReal| ≤ δ := by
  have law (path : GameCoherence.Path left right) : path.joint.bind observer =
      left.program.eval.bind (fun x => (path.kernel x).bind (fun y => observer (x,y))) := by
    rw [GameCoherence.Path.joint,PMF.bind_bind]
    apply congrArg (PMF.bind left.program.eval)
    funext x
    rw [PMF.bind_map]
    rfl
  rw [law p,law q,event_bind_real,event_bind_real,← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ x, |(left.program.eval x).toReal *
        ((eventProb ((p.kernel x).bind (fun y => observer (x,y))) event).toReal -
          (eventProb ((q.kernel x).bind (fun y => observer (x,y))) event).toReal)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ δ := cell.retained_observer_bound (fun x y => observer (x,y)) event

theorem joint_probability_gap {left right : Observed} [Fintype left.Outcome] [Fintype right.Outcome]
    {p q : GameCoherence.Path left right} {δ : ℝ} (cell : Cell4 p q δ) {T : Type}
    (observer : left.Outcome × right.Outcome → PMF T) (event : T → Prop) :
    probabilityGap (eventProb (p.joint.bind observer) event) (eventProb (q.joint.bind observer) event) ≤
      ENNReal.ofReal δ := by
  rw [probabilityGap_eq_ofReal_abs _ _
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))]
  exact ENNReal.ofReal_le_ofReal (cell.joint_observer_bound observer event)

end Cell4
end
end CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence
