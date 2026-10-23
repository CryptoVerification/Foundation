import Foundation.Logic.Polygraph.CartesianContext
import Foundation.Logic.Polygraph.Higher

/-! A finite schematic basis relative to the existing reconstruction
presentation. There are three root squares, one reconstruction loop, and five
one-hole reconstruction naturality squares. No generator is indexed by an
arbitrary structural step or path. This is not a presentation solely by
primitive copy/delete/symmetry gates: `reconstruct` remains a term schema. -/
namespace Foundation.Logic.Polygraph.Cartesian

universe j r
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {T : Presentation.{j, r}}

abbrev Vertex {Γ Δ : Logic.Context T} (F : Forest Γ Δ) :=
  {d : Diagram T Γ Δ // d.toForest = F}

def target {Γ Δ : Logic.Context T} (F : Forest Γ Δ) : Vertex F :=
  ⟨Diagram.ofForest F, Diagram.toForest_ofForest F⟩

def normal {Γ Δ : Logic.Context T} (F : Forest Γ Δ) (d : Vertex F) :
    Diagram.Cell3 d.val (Diagram.ofForest F) := by
  obtain ⟨d, h⟩ := d
  subst F
  exact .step (.reconstruct d)

namespace Place
variable {Γ Δ Θ Ξ : Logic.Context T}
def vertex (c : Place Γ Δ Θ Ξ) (F : Forest Γ Δ) (d : Vertex F) : Vertex (c.forest F) :=
  ⟨c.apply d.val, (c.forest_apply d.val).trans (congrArg c.forest d.property)⟩
end Place

/-- Exactly the three non-reconstruction root rules. -/
inductive Root : {Γ Δ : Logic.Context T} → Diagram T Γ Δ → Diagram T Γ Δ → Type (max j r) where
  | assoc {Γ Δ Θ Ξ} (f : Diagram T Γ Δ) (g : Diagram T Δ Θ) (h : Diagram T Θ Ξ) :
      Root (.seq (.seq f g) h) (.seq f (.seq g h))
  | leftUnit {Γ Δ} (f : Diagram T Γ Δ) : Root (.seq (.identity Γ) f) f
  | rightUnit {Γ Δ} (f : Diagram T Γ Δ) : Root (.seq f (.identity Δ)) f

def Root.step : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} → Root f g →
    Diagram.StructuralStep f g
  | _, _, _, _, .assoc f g h => .assoc f g h
  | _, _, _, _, .leftUnit f => .leftUnit f
  | _, _, _, _, .rightUnit f => .rightUnit f

inductive Generator : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    Diagram.Cell3 f g → Diagram.Cell3 f g → Type (max j r) where
  | root {Γ Δ} {f g : Diagram T Γ Δ} (s : Root f g) (F : Forest Γ Δ)
      (hf : f.toForest = F) :
      Generator (.comp (.step s.step) (normal F ⟨g, s.step.forest_eq.symm.trans hf⟩))
        (normal F ⟨f, hf⟩)
  | normalLoop {Γ Δ} (F : Forest (T := T) Γ Δ) :
      Generator (normal F (target F)) (.refl (Diagram.ofForest F))
  | contextReconstruct {Γ Δ Θ Ξ} (c : Place (T := T) Γ Δ Θ Ξ)
      (F : Forest Γ Δ) (d : Vertex F) :
      Generator (.comp (c.path (normal F d)) (normal (c.forest F) (c.vertex F (target F))))
        (normal (c.forest F) (c.vertex F d))

/-- An explicit bound on the number of schema forms; typed instances remain
unbounded. The five context cases are intentionally enumerated here. -/
def Root.code : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} → Root f g → Fin 9
  | _, _, _, _, .assoc _ _ _ => 0
  | _, _, _, _, .leftUnit _ => 1
  | _, _, _, _, .rightUnit _ => 2

def Place.code : {Γ Δ Θ Ξ : Logic.Context T} → Place Γ Δ Θ Ξ → Fin 9
  | _, _, _, _, .seqLeft _ => 4
  | _, _, _, _, .seqRight _ => 5
  | _, _, _, _, .tensorLeft _ => 6
  | _, _, _, _, .tensorRight _ => 7
  | _, _, _, _, .tupleAt _ _ => 8

def Generator.code : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    {p q : Diagram.Cell3 f g} → Generator p q → Fin 9
  | _, _, _, _, _, _, .root s _ _ => s.code
  | _, _, _, _, _, _, .normalLoop _ => 3
  | _, _, _, _, _, _, .contextReconstruct c _ _ => c.code

/-- Groupoid pasting and the five syntax contexts are structural operations. -/
inductive Cell4 : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    Diagram.Cell3 f g → Diagram.Cell3 f g → Type (max j r) where
  | generator {Γ Δ} {f g : Diagram T Γ Δ} {p q : Diagram.Cell3 f g} : Generator p q → Cell4 p q
  | law {Γ Δ} {f g : Diagram T Γ Δ} {p q : Diagram.Cell3 f g} :
      Four (fun {_ _} _ _ => PEmpty.{1}) p q → Cell4 p q
  | symm {Γ Δ} {f g : Diagram T Γ Δ} {p q : Diagram.Cell3 f g} : Cell4 p q → Cell4 q p
  | trans {Γ Δ} {f g : Diagram T Γ Δ} {p q s : Diagram.Cell3 f g} :
      Cell4 p q → Cell4 q s → Cell4 p s
  | comp {Γ Δ} {f g h : Diagram T Γ Δ} {p p' : Diagram.Cell3 f g} {q q' : Diagram.Cell3 g h} :
      Cell4 p p' → Cell4 q q' → Cell4 (.comp p q) (.comp p' q')
  | inverse {Γ Δ} {f g : Diagram T Γ Δ} {p q : Diagram.Cell3 f g} :
      Cell4 p q → Cell4 (.inv p) (.inv q)
  | inContext {Γ Δ Θ Ξ} (c : Place Γ Δ Θ Ξ) {f g : Diagram T Γ Δ} {p q : Diagram.Cell3 f g} :
      Cell4 p q → Cell4 (c.path p) (c.path q)

namespace Cell4
variable {Γ Δ : Logic.Context T} {f g h i : Diagram T Γ Δ}
def refl (p : Diagram.Cell3 f g) : Cell4 p p := .law (.refl p)
def assoc (p : Diagram.Cell3 f g) (q : Diagram.Cell3 g h) (s : Diagram.Cell3 h i) :
    Cell4 (.comp (.comp p q) s) (.comp p (.comp q s)) := .law (.assoc p q s)
def leftUnit (p : Diagram.Cell3 f g) : Cell4 (.comp (.refl f) p) p := .law (.leftUnit p)
def rightUnit (p : Diagram.Cell3 f g) : Cell4 (.comp p (.refl g)) p := .law (.rightUnit p)
def leftInv (p : Diagram.Cell3 f g) : Cell4 (.comp (.inv p) p) (.refl g) := .law (.leftInv p)
def rightInv (p : Diagram.Cell3 f g) : Cell4 (.comp p (.inv p)) (.refl f) := .law (.rightInv p)
end Cell4

/-- Reconstruction naturality for an arbitrary step is derived recursively,
rather than being a primitive square schema. -/
def underContext {Γ Δ Θ Ξ : Logic.Context T} (c : Place Γ Δ Θ Ξ)
    {f g : Diagram T Γ Δ} (s : Diagram.StructuralStep f g)
    (ih : Cell4 (.comp (.step s) (normal f.toForest ⟨g, s.forest_eq.symm⟩))
      (normal f.toForest ⟨f, rfl⟩)) :
    Cell4 (.comp (.step (c.step s))
      (normal (c.forest f.toForest) (c.vertex f.toForest ⟨g, s.forest_eq.symm⟩)))
      (normal (c.forest f.toForest) (c.vertex f.toForest ⟨f, rfl⟩)) :=
  (Cell4.comp (.refl (.step (c.step s)))
    (Cell4.generator (.contextReconstruct c f.toForest ⟨g, s.forest_eq.symm⟩)).symm).trans
    ((Cell4.assoc (.step (c.step s)) _ _).symm.trans
      ((Cell4.comp (.inContext c ih) (.refl _)).trans
        (.generator (.contextReconstruct c f.toForest ⟨f, rfl⟩))))

def contextualSquare {Γ Δ Θ Ξ : Logic.Context T} (c : Place Γ Δ Θ Ξ)
    {f g : Diagram T Γ Δ} (s : Diagram.StructuralStep f g)
    (ih : Cell4 (.comp (.step s) (normal f.toForest ⟨g, s.forest_eq.symm⟩))
      (normal f.toForest ⟨f, rfl⟩))
    (F : Forest Θ Ξ) (hf : (c.apply f).toForest = F) :
    Cell4 (.comp (.step (c.step s))
      (normal F ⟨c.apply g, (c.step s).forest_eq.symm.trans hf⟩))
      (normal F ⟨c.apply f, hf⟩) := by
  have e : c.forest f.toForest = F := (c.forest_apply f).symm.trans hf
  cases e
  exact underContext c s ih

def stepSquare : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    (s : Diagram.StructuralStep f g) → (F : Forest Γ Δ) → (hf : f.toForest = F) →
    Cell4 (.comp (.step s) (normal F ⟨g, s.forest_eq.symm.trans hf⟩)) (normal F ⟨f, hf⟩)
  | _, _, _, _, .assoc f g h, F, hf => .generator (.root (.assoc f g h) F hf)
  | _, _, _, _, .leftUnit f, F, hf => .generator (.root (.leftUnit f) F hf)
  | _, _, _, _, .rightUnit f, F, hf => .generator (.root (.rightUnit f) F hf)
  | _, _, _, _, .reconstruct f, F, hf => by
      subst F
      exact (Cell4.comp (.refl (.step (.reconstruct f)))
        (.generator (.normalLoop f.toForest))).trans (.rightUnit _)
  | _, _, _, _, .seqLeft s g, F, hf =>
      contextualSquare (.seqLeft g) s (stepSquare s _ rfl) F hf
  | _, _, _, _, .seqRight f s, F, hf =>
      contextualSquare (.seqRight f) s (stepSquare s _ rfl) F hf
  | _, _, _, _, .tensorLeft s g, F, hf =>
      contextualSquare (.tensorLeft g) s (stepSquare s _ rfl) F hf
  | _, _, _, _, .tensorRight f s, F, hf =>
      contextualSquare (.tensorRight f) s (stepSquare s _ rfl) F hf
  | _, _, _, _, .tupleAt children i s, F, hf =>
      contextualSquare (.tupleAt children i) s (stepSquare s _ rfl) F hf

def contract : {Γ Δ : Logic.Context T} → {f g : Diagram T Γ Δ} →
    (p : Diagram.Cell3 f g) → (F : Forest Γ Δ) → (hf : f.toForest = F) →
    (hg : g.toForest = F) → Cell4 (.comp p (normal F ⟨g, hg⟩)) (normal F ⟨f, hf⟩)
  | _, _, _, _, .refl _, _, _, _ => .leftUnit _
  | _, _, _, _, .step s, F, hf, _ => stepSquare s F hf
  | _, _, _, _, .comp p q, F, hf, hg =>
      (Cell4.assoc p q _).trans
        ((Cell4.comp (.refl p) (contract q F ((Diagram.Cell3.forest_eq p).symm.trans hf) hg)).trans
          (contract p F hf ((Diagram.Cell3.forest_eq p).symm.trans hf)))
  | _, _, _, _, .inv p, F, hf, hg =>
      (Cell4.comp (.refl (.inv p)) (contract p F hg hf).symm).trans
        ((Cell4.assoc (.inv p) p _).symm.trans
          ((Cell4.comp (.leftInv p) (.refl _)).trans (.leftUnit _)))

def factor {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ} (p : Diagram.Cell3 f g)
    (F : Forest Γ Δ) (hf : f.toForest = F) (hg : g.toForest = F) :
    Cell4 p (.comp (normal F ⟨f, hf⟩) (.inv (normal F ⟨g, hg⟩))) :=
  (Cell4.rightUnit p).symm.trans
    ((Cell4.comp (.refl p) (Cell4.rightInv (normal F ⟨g, hg⟩)).symm).trans
      ((Cell4.assoc p _ _).symm.trans
        (Cell4.comp (contract p F hf hg) (.refl _))))

/-- Every parallel pair of full structural paths admits a four-cell built
from the nine diagram forms (3 roots + loop + 5 contexts). -/
def coherent {Γ Δ : Logic.Context T} {f g : Diagram T Γ Δ} (p q : Diagram.Cell3 f g) :
    Cell4 p q :=
  (factor p f.toForest rfl p.forest_eq.symm).trans
    (factor q f.toForest rfl p.forest_eq.symm).symm

end Foundation.Logic.Polygraph.Cartesian
