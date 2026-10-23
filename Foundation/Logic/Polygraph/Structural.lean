import Foundation.Logic.Polygraph.Cell
import Foundation.Logic.Polygraph.Rewriting
import Mathlib.Logic.Function.Basic

/-! A schematic cartesian presentation on raw diagrams. `reconstruct` is the
term-expansion schema for all diagram constructors, including logical copying
and discarding. It is deliberately not oriented as a terminating rewrite rule.
The separate Composition system is the terminating association/unit fragment. -/
namespace Foundation.Logic.Polygraph.Diagram

universe j r v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {T : Presentation.{j, r}}

theorem toForest_tupleAt_congr {Γ Δ : Logic.Context T}
    (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
    {f g : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} (h : f.toForest = g.toForest) :
    (Diagram.tuple (Function.update children i f)).toForest =
      (Diagram.tuple (Function.update children i g)).toForest := by
  funext k
  by_cases hk : k = i
  · subst k
    simpa only [toForest, Function.update_self] using congrFun h 0
  · simp only [toForest, Function.update_of_ne hk]

inductive StructuralStep : {Γ Δ : Logic.Context T} →
    Diagram T Γ Δ → Diagram T Γ Δ → Type (max j r) where
  | assoc {Γ Δ Θ Ξ} (f : Diagram T Γ Δ) (g : Diagram T Δ Θ) (h : Diagram T Θ Ξ) :
      StructuralStep (.seq (.seq f g) h) (.seq f (.seq g h))
  | leftUnit {Γ Δ} (f : Diagram T Γ Δ) : StructuralStep (.seq (.identity Γ) f) f
  | rightUnit {Γ Δ} (f : Diagram T Γ Δ) : StructuralStep (.seq f (.identity Δ)) f
  | reconstruct {Γ Δ} (f : Diagram T Γ Δ) : StructuralStep f (ofForest f.toForest)
  | seqLeft {Γ Δ Θ} {f f' : Diagram T Γ Δ} (s : StructuralStep f f') (g : Diagram T Δ Θ) :
      StructuralStep (.seq f g) (.seq f' g)
  | seqRight {Γ Δ Θ} (f : Diagram T Γ Δ) {g g' : Diagram T Δ Θ} (s : StructuralStep g g') :
      StructuralStep (.seq f g) (.seq f g')
  | tensorLeft {Γ Δ Γ' Δ'} {f f' : Diagram T Γ Δ} (s : StructuralStep f f')
      (g : Diagram T Γ' Δ') : StructuralStep (.tensor f g) (.tensor f' g)
  | tensorRight {Γ Δ Γ' Δ'} (f : Diagram T Γ Δ) {g g' : Diagram T Γ' Δ'}
      (s : StructuralStep g g') : StructuralStep (.tensor f g) (.tensor f g')
  | tupleAt {Γ Δ : Logic.Context T}
      (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
      {f g : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} (s : StructuralStep f g) :
      StructuralStep (.tuple (Function.update children i f)) (.tuple (Function.update children i g))

theorem StructuralStep.forest_eq {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ}
    (s : StructuralStep f g) : f.toForest = g.toForest := by
  induction s with
  | assoc => exact toForest_seq_assoc _ _ _
  | leftUnit => exact toForest_identity_seq _
  | rightUnit => rfl
  | reconstruct => exact (toForest_ofForest _).symm
  | seqLeft s g ih => simp only [toForest, ih]
  | seqRight f s ih => simp only [toForest, ih]
  | tensorLeft s g ih => simp only [toForest, ih]
  | tensorRight f s ih => simp only [toForest, ih]
  | tupleAt children i s ih => exact toForest_tupleAt_congr children i ih

abbrev Cell3 {Γ Δ : Logic.Context T} (f g : Diagram T Γ Δ) :=
  Track (@StructuralStep T Γ Δ) f g

theorem Cell3.forest_eq {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ}
    (p : Cell3 f g) : f.toForest = g.toForest := by
  induction p with
  | refl => rfl
  | step s => exact s.forest_eq
  | comp p q ihp ihq => exact ihp.trans ihq
  | inv p ih => exact ih.symm

/-- Completeness for the specified cartesian term presentation. This cannot
connect different formal rule trees merely because their boundaries agree. -/
def connect {Γ Δ : Logic.Context T} (f g : Diagram T Γ Δ)
    (h : f.toForest = g.toForest) : Cell3 f g :=
  .comp (.step (.reconstruct f))
    (congrArg ofForest h ▸ Track.inv (Track.step (StructuralStep.reconstruct g)))

def Cell3.seqLeft {Γ Δ Θ : Logic.Context T} {f f' : Diagram T Γ Δ}
    (p : Cell3 f f') (g : Diagram T Δ Θ) : Cell3 (.seq f g) (.seq f' g) :=
  p.map (S := fun x y => StructuralStep x y) (fun f => Diagram.seq f g)
    (fun s => StructuralStep.seqLeft s g)

def Cell3.seqRight {Γ Δ Θ : Logic.Context T} (f : Diagram T Γ Δ)
    {g g' : Diagram T Δ Θ} (p : Cell3 g g') : Cell3 (.seq f g) (.seq f g') :=
  p.map (S := fun x y => StructuralStep x y) (fun g => Diagram.seq f g)
    (fun s => StructuralStep.seqRight f s)

def Cell3.tensorLeft {Γ Δ Γ' Δ' : Logic.Context T} {f f' : Diagram T Γ Δ}
    (p : Cell3 f f') (g : Diagram T Γ' Δ') : Cell3 (.tensor f g) (.tensor f' g) :=
  p.map (S := fun x y => StructuralStep x y) (fun f => Diagram.tensor f g)
    (fun s => StructuralStep.tensorLeft s g)

def Cell3.tensorRight {Γ Δ Γ' Δ' : Logic.Context T} (f : Diagram T Γ Δ)
    {g g' : Diagram T Γ' Δ'} (p : Cell3 g g') : Cell3 (.tensor f g) (.tensor f g') :=
  p.map (S := fun x y => StructuralStep x y) (fun g => Diagram.tensor f g)
    (fun s => StructuralStep.tensorRight f s)

def Cell3.tuple {Γ Δ : Logic.Context T}
    {f g : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))}
    (p : ∀ i, Cell3 (f i) (g i)) : Cell3 (.tuple f) (.tuple g) :=
  connect _ _ (funext (fun i => congrFun (p i).forest_eq 0))

def Cell3.tupleAt {Γ Δ : Logic.Context T}
    (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length)
    {f g : Diagram T Γ (Logic.Context.singleton (Δ.claim i))} (p : Cell3 f g) :
    Cell3 (.tuple (Function.update children i f)) (.tuple (Function.update children i g)) :=
  p.map (S := fun x y => StructuralStep x y)
    (fun f => Diagram.tuple (Function.update children i f))
    (fun s => StructuralStep.tupleAt children i s)

theorem Cell3.eval_eq {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ}
    (p : Cell3 f g) (M : Model.{j, r, v} T) (env : Environment M Γ) :
    f.eval M env = g.eval M env := by
  funext i
  rw [← eval_toForest, ← eval_toForest, p.forest_eq]

end Foundation.Logic.Polygraph.Diagram
