import Foundation.Logic.Polygraph.Structural
import Foundation.Logic.Polygraph.Higher
import Mathlib.Logic.Function.Basic

/-! User-specified three- and four-generators with parallel composite
boundaries. Three-dimensional rewriting is closed under sequential and tensor
contexts and finite tuples. Semantic preservation is a separate obligation
for each registered generator, never inferred just from its boundary. -/
namespace Foundation.Logic.Polygraph

universe j r s t v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

structure Presentation3 (T : Presentation.{j, r}) where
  Generator : {Γ Δ : Logic.Context T} → Diagram T Γ Δ → Diagram T Γ Δ → Type s

namespace Presentation3
variable {T : Presentation.{j, r}} (P : Presentation3.{j, r, s} T)

inductive Step : {Γ Δ : Logic.Context T} → Diagram T Γ Δ → Diagram T Γ Δ →
    Type (max j r s) where
  | generator {Γ Δ} {f g : Diagram T Γ Δ} : P.Generator f g → Step f g
  | structural {Γ Δ} {f g : Diagram T Γ Δ} : Diagram.StructuralStep f g → Step f g
  | identity {Γ Δ} (f : Diagram T Γ Δ) : Step f f
  | seqLeft {Γ Δ Θ} {f f' : Diagram T Γ Δ} (p : Step f f') (g : Diagram T Δ Θ) :
      Step (.seq f g) (.seq f' g)
  | seqRight {Γ Δ Θ} (f : Diagram T Γ Δ) {g g' : Diagram T Δ Θ} (p : Step g g') :
      Step (.seq f g) (.seq f g')
  | tensorLeft {Γ Δ Γ' Δ'} {f f' : Diagram T Γ Δ} (p : Step f f')
      (g : Diagram T Γ' Δ') : Step (.tensor f g) (.tensor f' g)
  | tensorRight {Γ Δ Γ' Δ'} (f : Diagram T Γ Δ) {g g' : Diagram T Γ' Δ'}
      (p : Step g g') : Step (.tensor f g) (.tensor f g')
  | tuple {Γ Δ : Logic.Context T} {f g : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))}
      (p : ∀ i, Step (f i) (g i)) : Step (.tuple f) (.tuple g)

abbrev Cell3 {Γ Δ : Logic.Context T} (f g : Diagram T Γ Δ) := Track (@Step T P Γ Δ) f g

def Cell3.seqLeft {Γ Δ Θ : Logic.Context T} {f f' : Diagram T Γ Δ}
    (p : P.Cell3 f f') (g : Diagram T Δ Θ) : P.Cell3 (.seq f g) (.seq f' g) :=
  p.map (S := fun x y => P.Step x y) (fun f => Diagram.seq f g) (fun s => .seqLeft s g)

def Cell3.seqRight {Γ Δ Θ : Logic.Context T} (f : Diagram T Γ Δ)
    {g g' : Diagram T Δ Θ} (p : P.Cell3 g g') : P.Cell3 (.seq f g) (.seq f g') :=
  p.map (S := fun x y => P.Step x y) (fun g => Diagram.seq f g) (fun s => .seqRight f s)

def Cell3.tensorLeft {Γ Δ Γ' Δ' : Logic.Context T} {f f' : Diagram T Γ Δ}
    (p : P.Cell3 f f') (g : Diagram T Γ' Δ') : P.Cell3 (.tensor f g) (.tensor f' g) :=
  p.map (S := fun x y => P.Step x y) (fun f => Diagram.tensor f g) (fun s => .tensorLeft s g)

def Cell3.tensorRight {Γ Δ Γ' Δ' : Logic.Context T} (f : Diagram T Γ Δ)
    {g g' : Diagram T Γ' Δ'} (p : P.Cell3 g g') : P.Cell3 (.tensor f g) (.tensor f g') :=
  p.map (S := fun x y => P.Step x y) (fun g => Diagram.tensor f g) (fun s => .tensorRight f s)

def tupleAtStep {Γ Δ : Logic.Context T}
    (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
    {a b : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} (s : P.Step a b) :
    P.Step (.tuple (Function.update children i a)) (.tuple (Function.update children i b)) := by
  apply Step.tuple
  intro j
  by_cases hj : j = i
  · subst j; simpa using s
  · simpa [Function.update_of_ne hj] using (Step.identity (P := P) (children j))

def Cell3.tupleAt {Γ Δ : Logic.Context T}
    (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
    {a b : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} (p : P.Cell3 a b) :
    P.Cell3 (.tuple (Function.update children i a)) (.tuple (Function.update children i b)) :=
  p.map (S := fun x y => P.Step x y) (fun a => Diagram.tuple (Function.update children i a))
    (fun s => tupleAtStep P children i s)

/-- The selected model may retain code, losses, trees, or full certificates.
A generator preserving one model need not preserve any other model. -/
def Respects (M : Model.{j, r, v} T) : Prop :=
  ∀ {Γ Δ} {f g : Diagram T Γ Δ}, P.Generator f g → ∀ env, f.eval M env = g.eval M env

theorem Step.eval_eq (M : Model.{j, r, v} T) (h : P.Respects M)
    {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ} (step : P.Step f g) :
    ∀ env, f.eval M env = g.eval M env := by
  induction step with
  | generator g => exact h g
  | structural s => exact fun env => Diagram.Cell3.eval_eq (.step s) M env
  | identity => exact fun _ => rfl
  | seqLeft p g ih => intro env; simp only [Diagram.eval, ih]
  | seqRight f p ih => intro env; exact ih _
  | tensorLeft p g ih =>
      intro env
      simp only [Diagram.eval, ih]
  | tensorRight f p ih =>
      intro env
      simp only [Diagram.eval, ih]
  | tuple p ih =>
      intro env
      funext i
      exact congrFun (ih i env) 0

theorem Cell3.eval_eq (M : Model.{j, r, v} T) (h : P.Respects M)
    {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ} (path : P.Cell3 f g) :
    ∀ env, f.eval M env = g.eval M env := by
  induction path with
  | refl => exact fun _ => rfl
  | step s => exact Step.eval_eq P M h s
  | comp p q ihp ihq => exact fun env => (ihp env).trans (ihq env)
  | inv p ih => exact fun env => (ih env).symm

end Presentation3

structure Presentation4 {T : Presentation.{j, r}} (P : Presentation3.{j, r, s} T) where
  Generator : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    P.Cell3 f g → P.Cell3 f g → Type t

namespace Presentation4
variable {T : Presentation.{j, r}} {P : Presentation3.{j, r, s} T}
  (Q : Presentation4.{j, r, s, t} P)

/-- Four-dimensional pasting, also closed under lower-dimensional contexts. -/
inductive Cell4 : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    P.Cell3 f g → P.Cell3 f g → Type (max j r s t) where
  | base {Γ Δ} {f g : Diagram T Γ Δ} {p q : P.Cell3 f g} :
      Four (fun {a b} => @Q.Generator Γ Δ a b) p q → Cell4 p q
  | symm {Γ Δ} {f g : Diagram T Γ Δ} {p q : P.Cell3 f g} : Cell4 p q → Cell4 q p
  | trans {Γ Δ} {f g : Diagram T Γ Δ} {p q r : P.Cell3 f g} :
      Cell4 p q → Cell4 q r → Cell4 p r
  | comp {Γ Δ} {f g h : Diagram T Γ Δ} {p p' : P.Cell3 f g} {q q' : P.Cell3 g h} :
      Cell4 p p' → Cell4 q q' → Cell4 (.comp p q) (.comp p' q')
  | inverse {Γ Δ} {f g : Diagram T Γ Δ} {p q : P.Cell3 f g} :
      Cell4 p q → Cell4 (.inv p) (.inv q)
  | seqLeft {Γ Δ Θ} {f f' : Diagram T Γ Δ} {p q : P.Cell3 f f'}
      (h : Cell4 p q) (g : Diagram T Δ Θ) :
      Cell4 (Presentation3.Cell3.seqLeft P p g) (Presentation3.Cell3.seqLeft P q g)
  | seqRight {Γ Δ Θ} (f : Diagram T Γ Δ) {g g' : Diagram T Δ Θ} {p q : P.Cell3 g g'}
      (h : Cell4 p q) :
      Cell4 (Presentation3.Cell3.seqRight P f p) (Presentation3.Cell3.seqRight P f q)
  | tensorLeft {Γ Δ Γ' Δ'} {f f' : Diagram T Γ Δ} {p q : P.Cell3 f f'}
      (h : Cell4 p q) (g : Diagram T Γ' Δ') :
      Cell4 (Presentation3.Cell3.tensorLeft P p g) (Presentation3.Cell3.tensorLeft P q g)
  | tensorRight {Γ Δ Γ' Δ'} (f : Diagram T Γ Δ) {g g' : Diagram T Γ' Δ'}
      {p q : P.Cell3 g g'} (h : Cell4 p q) :
      Cell4 (Presentation3.Cell3.tensorRight P f p) (Presentation3.Cell3.tensorRight P f q)
  | tupleAt {Γ Δ : Logic.Context T}
      (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
      {a b : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} {p q : P.Cell3 a b}
      (h : Cell4 p q) :
      Cell4 (Presentation3.Cell3.tupleAt P children i p) (Presentation3.Cell3.tupleAt P children i q)

end Presentation4

end Foundation.Logic.Polygraph
