import Foundation.Crypto.Logic.Polygraph.Experiment
import Foundation.Logic.Polygraph.Rewriting
import Foundation.Crypto.Semantics.Probability.Coupling
import Foundation.Crypto.Semantics.Security.ThreeGames

/-! A separate experiment layer. Exact transformations compare full laws;
statistical hops compare specified observations with directional loss bounds;
computational hops retain certified compilers and execution evidence. Logical
contraction is not a rule for executing a probabilistic computation twice. -/
namespace CryptoLogic.Polygraph.Experiment

open Foundation.Probability Foundation.Logic.Polygraph
open scoped ENNReal
universe u v
set_option linter.checkUnivs false

inductive Program : Type u → Type (u + 1) where
  | pure {α} : α → Program α
  | sample {α} : PMF α → Program α
  | bind {α β} : Program α → (α → Program β) → Program β

namespace Program

noncomputable def eval : {α : Type u} → Program α → PMF α
  | _, .pure a => PMF.pure a
  | _, .sample p => p
  | _, .bind p k => (eval p).bind (fun a => eval (k a))

def map {α β : Type u} (p : Program α) (f : α → β) : Program β :=
  .bind p (fun a => .pure (f a))

end Program

inductive ExactStep : {α : Type u} → Program α → Program α → Type (u + 1) where
  | leftUnit {α β} (a : α) (k : α → Program β) :
      ExactStep (.bind (.pure a) k) (k a)
  | rightUnit {α} (p : Program α) : ExactStep (.bind p .pure) p
  | assoc {α β γ} (p : Program α) (k : α → Program β) (h : β → Program γ) :
      ExactStep (.bind (.bind p k) h) (.bind p (fun a => .bind (k a) h))
  | distribution {α} {p q : PMF α} (h : p = q) : ExactStep (.sample p) (.sample q)
  | reindex {α β γ} (p : PMF α) (e : α ≃ β) (k : β → Program γ) :
      ExactStep (.bind (.sample (p.map e)) k) (.bind (.sample p) (fun a => k (e a)))
  | independent {α β γ} (p : PMF α) (q : PMF β) (k : α → β → Program γ) :
      ExactStep (.bind (.sample p) (fun a => .bind (.sample q) (k a)))
        (.bind (.sample q) (fun b => .bind (.sample p) (fun a => k a b)))
  | bindFirst {α β} {p q : Program α} (s : ExactStep p q) (k : α → Program β) :
      ExactStep (.bind p k) (.bind q k)
  | bindThen {α β} (p : Program α) {k h : α → Program β} (s : ∀ a, ExactStep (k a) (h a)) :
      ExactStep (.bind p k) (.bind p h)

theorem ExactStep.sound {α : Type u} {p q : Program α} (s : ExactStep p q) :
    p.eval = q.eval := by
  induction s with
  | leftUnit => exact PMF.pure_bind _ _
  | rightUnit => exact PMF.bind_pure _
  | assoc => exact PMF.bind_bind _ _ _
  | distribution h => exact h
  | reindex => exact PMF.bind_map _ _ _
  | independent => exact PMF.bind_comm _ _ _
  | bindFirst s k ih => exact congrArg (fun law => law.bind (fun a => (k a).eval)) ih
  | bindThen p s ih => exact congrArg (PMF.bind p.eval) (funext ih)

abbrev ExactPath {α : Type u} (p q : Program α) := Track (@ExactStep α) p q

theorem ExactPath.sound {α : Type u} {p q : Program α} (path : ExactPath p q) :
    p.eval = q.eval := by
  induction path with
  | refl => rfl
  | step s => exact s.sound
  | comp p q ihp ihq => exact ihp.trans ihq
  | inv p ih => exact ih.symm

structure Observed where
  Outcome : Type u
  program : Program Outcome
  event : Outcome → Prop

noncomputable def Observed.probability (o : Observed.{u}) : ℝ≥0∞ :=
  eventProb o.program.eval o.event

inductive Hop : Observed.{u} → Observed.{u} → ℝ≥0∞ → Type (u + 1) where
  | exact {α : Type u} {p q : Program α} (path : ExactPath p q) (event : α → Prop) :
      Hop ⟨α, p, event⟩ ⟨α, q, event⟩ 0
  | coupling {left right : Observed.{u}} {Joint : Type u}
      (joint : PMF Joint) (projectLeft : Joint → left.Outcome)
      (projectRight : Joint → right.Outcome)
      (leftMarginal : joint.map projectLeft = left.program.eval)
      (rightMarginal : joint.map projectRight = right.program.eval)
      (bad : Joint → Prop)
      (agree : ∀ x ∈ joint.support, ¬bad x →
        (left.event (projectLeft x) ↔ right.event (projectRight x))) :
      Hop left right (eventProb joint bad)
  | comp {left middle right} {ε δ} : Hop left middle ε → Hop middle right δ →
      Hop left right (ε + δ)
  | weaken {left right} {ε δ} : Hop left right ε → ε ≤ δ → Hop left right δ

theorem Hop.sound {left right : Observed.{u}} {ε} (hop : Hop left right ε) :
    probabilityGap left.probability right.probability ≤ ε := by
  induction hop with
  | exact path event => simp [Observed.probability, path.sound, probabilityGap]
  | coupling joint pl pr hl hr bad agree =>
      exact coupled_map_gap_le joint _ _ pl pr hl hr _ _ bad agree
  | comp p q ihp ihq =>
      exact (ThreeGames.probabilityGap_triangle _ _ _).trans (add_le_add ihp ihq)
  | weaken p h ih => exact ih.trans h

/-- Computational replacement is a different syntax, carrying a certified
machine reduction rather than merely a number attached to a statistical hop. -/
inductive ComputationalPath {K : General.CodeSystem} :
    {m n : K.Machine} → General.SecurityObject.{u, v} K m →
      General.SecurityObject.{u, v} K n → Type (max (u + 1) (v + 1)) where
  | identity {m} (X : General.SecurityObject.{u, v} K m) : ComputationalPath X X
  | reduction {m n} {X : General.SecurityObject.{u, v} K m}
      {Y : General.SecurityObject.{u, v} K n} :
      General.CertifiedReduction X Y → ComputationalPath X Y
  | comp {m n k} {X : General.SecurityObject.{u, v} K m}
      {Y : General.SecurityObject.{u, v} K n} {Z : General.SecurityObject.{u, v} K k} :
      ComputationalPath X Y → ComputationalPath Y Z → ComputationalPath X Z

def ComputationalPath.eval {K : General.CodeSystem} :
    {m n : K.Machine} → {X : General.SecurityObject.{u, v} K m} →
      {Y : General.SecurityObject.{u, v} K n} → ComputationalPath X Y → General.CertifiedReduction X Y
  | _, _, _, _, .identity X => .id X
  | _, _, _, _, .reduction r => r
  | _, _, _, _, .comp p q => (eval p).comp (eval q)

theorem ComputationalPath.secure {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{u, v} K m} {Y : General.SecurityObject.{u, v} K n}
    (path : ComputationalPath X Y) (F) (h : Y.Secure (path.eval.reduction.mapFamily F)) :
    X.Secure F := path.eval.secure F h

theorem ComputationalPath.code_eq {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{u, v} K m} {Y : General.SecurityObject.{u, v} K n}
    (path : ComputationalPath X Y) (F A) (W : X.Witness F A) :
    (path.eval.mapWitness F A W).code = path.eval.compiler.run W.code :=
  path.eval.code_eq F A W

theorem ComputationalPath.executes {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{u, v} K m} {Y : General.SecurityObject.{u, v} K n}
    (path : ComputationalPath X Y) (F A) (W : X.Witness F A) :
    Y.execution.ExecutesWithin (path.eval.reduction.mapFamily F)
      (path.eval.compiler.run W.code) (path.eval.mapWitness F A W).resources :=
  path.eval.toTransform.compiler_executes F A W

theorem ComputationalPath.realizes {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{u, v} K m} {Y : General.SecurityObject.{u, v} K n}
    (path : ComputationalPath X Y) (F A) (W : X.Witness F A) :
    Y.execution.Realizes (path.eval.reduction.mapFamily F)
      (path.eval.reduction.mapAdversaryFamily F A) (path.eval.compiler.run W.code)
      (path.eval.mapWitness F A W).resources :=
  path.eval.toTransform.compiler_realizes F A W

end CryptoLogic.Polygraph.Experiment
