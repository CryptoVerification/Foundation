import Foundation.Logic.Polygraph.Structural

/-! The five one-hole contexts of the full inference-diagram syntax. In
particular a tuple context retains the position of a changed shared output,
rather than reconstructing and forgetting its original transformation path. -/
namespace Foundation.Logic.Polygraph.Cartesian

universe j r
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {T : Presentation.{j, r}}

inductive Place : Logic.Context T → Logic.Context T →
    Logic.Context T → Logic.Context T → Type (max j r) where
  | seqLeft {Γ Δ Θ} (g : Diagram T Δ Θ) : Place Γ Δ Γ Θ
  | seqRight {Γ Δ Θ} (f : Diagram T Γ Δ) : Place Δ Θ Γ Θ
  | tensorLeft {Γ Δ Γ' Δ'} (g : Diagram T Γ' Δ') :
      Place Γ Δ (Context.append Γ Γ') (Context.append Δ Δ')
  | tensorRight {Γ Δ Γ' Δ'} (f : Diagram T Γ Δ) :
      Place Γ' Δ' (Context.append Γ Γ') (Context.append Δ Δ')
  | tupleAt {Γ Δ : Logic.Context T}
      (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) (i : Fin Δ.length) :
      Place Γ (Logic.Context.singleton (Δ.claim i)) Γ Δ

namespace Place
variable {Γ Δ Θ Ξ : Logic.Context T}

def apply : {Γ Δ Θ Ξ : Logic.Context T} → Place Γ Δ Θ Ξ → Diagram T Γ Δ → Diagram T Θ Ξ
  | _, _, _, _, .seqLeft g, d => .seq d g
  | _, _, _, _, .seqRight f, d => .seq f d
  | _, _, _, _, .tensorLeft g, d => .tensor d g
  | _, _, _, _, .tensorRight f, d => .tensor f d
  | _, _, _, _, .tupleAt children i, d => .tuple (Function.update children i d)

def step : {Γ Δ Θ Ξ : Logic.Context T} → (c : Place Γ Δ Θ Ξ) →
    {f g : Diagram T Γ Δ} → Diagram.StructuralStep f g →
      Diagram.StructuralStep (c.apply f) (c.apply g)
  | _, _, _, _, .seqLeft g, _, _, s => .seqLeft s g
  | _, _, _, _, .seqRight f, _, _, s => .seqRight f s
  | _, _, _, _, .tensorLeft g, _, _, s => .tensorLeft s g
  | _, _, _, _, .tensorRight f, _, _, s => .tensorRight f s
  | _, _, _, _, .tupleAt children i, _, _, s => .tupleAt children i s

def path (c : Place Γ Δ Θ Ξ) {f g : Diagram T Γ Δ} (p : Diagram.Cell3 f g) :
    Diagram.Cell3 (c.apply f) (c.apply g) :=
  p.map (S := fun x y => Diagram.StructuralStep x y) c.apply (fun s => c.step s)

theorem forest_congr (c : Place Γ Δ Θ Ξ) {f g : Diagram T Γ Δ}
    (h : f.toForest = g.toForest) : (c.apply f).toForest = (c.apply g).toForest := by
  cases c with
  | seqLeft g => simp only [apply, Diagram.toForest, h]
  | seqRight f => simp only [apply, Diagram.toForest, h]
  | tensorLeft g => simp only [apply, Diagram.toForest, h]
  | tensorRight f => simp only [apply, Diagram.toForest, h]
  | tupleAt children i => exact Diagram.toForest_tupleAt_congr children i h

def forest (c : Place Γ Δ Θ Ξ) (f : Forest Γ Δ) : Forest Θ Ξ :=
  (c.apply (Diagram.ofForest f)).toForest

theorem forest_apply (c : Place Γ Δ Θ Ξ) (d : Diagram T Γ Δ) :
    (c.apply d).toForest = c.forest d.toForest :=
  c.forest_congr (Diagram.toForest_ofForest d.toForest).symm

end Place
end Foundation.Logic.Polygraph.Cartesian
