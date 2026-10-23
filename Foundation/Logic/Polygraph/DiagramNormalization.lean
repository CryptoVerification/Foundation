import Foundation.Logic.Polygraph.Coherence

/-! The convergent typed composition calculus acts on inference diagrams.
Recursive normalization also visits tensors and tuples. Every invocation
returns its original three-path, so all proof-relevant interpretations can be
transported along the same certificate. -/
namespace Foundation.Logic.Polygraph.Diagram

universe j r
set_option linter.checkUnivs false
variable {T : Presentation.{j, r}}

abbrev Composition (T : Presentation.{j, r}) :=
  Polygraph.Composition.Expr (Diagram T)

def quoteComposition : {Γ Δ : Logic.Context T} → Diagram T Γ Δ → Composition T Γ Δ
  | _, _, .identity Γ => .identity Γ
  | _, _, .seq f g => .seq (quoteComposition f) (quoteComposition g)
  | _, _, d => .atom d

def denoteComposition : {Γ Δ : Logic.Context T} → Composition T Γ Δ → Diagram T Γ Δ
  | _, _, .identity Γ => .identity Γ
  | _, _, .atom d => d
  | _, _, .seq f g => .seq (denoteComposition f) (denoteComposition g)

@[simp] theorem denote_quote {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    denoteComposition (quoteComposition d) = d := by
  induction d <;> simp_all [quoteComposition, denoteComposition]

def compositionStep : {Γ Δ : Logic.Context T} → {f g : Composition T Γ Δ} →
    Polygraph.Composition.Expr.Step f g →
    StructuralStep (denoteComposition f) (denoteComposition g)
  | _, _, _, _, .assoc _ _ _ => .assoc _ _ _
  | _, _, _, _, .leftUnit _ => .leftUnit _
  | _, _, _, _, .rightUnit _ => .rightUnit _
  | _, _, _, _, .left s _ => .seqLeft (compositionStep s) _
  | _, _, _, _, .right _ s => .seqRight _ (compositionStep s)

def normalizeTop {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) : Diagram T Γ Δ :=
  denoteComposition (quoteComposition d).normal

def normalizeTopPath {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) : Cell3 d (normalizeTop d) :=
  .comp (Track.ofEq (denote_quote d).symm) (Track.ofPath
    ((Polygraph.Composition.Expr.normalizePath (quoteComposition d)).map
      denoteComposition (fun s => compositionStep s)))

/-- Simultaneous syntax and certificate construction; no chosen semantic
model is needed to run this normalization algorithm. -/
def normalizeWithPath : {Γ Δ : Logic.Context T} → (d : Diagram T Γ Δ) →
    Σ n : Diagram T Γ Δ, Cell3 d n
  | _, _, .identity Γ => ⟨.identity Γ, .refl _⟩
  | _, _, .generator r => ⟨.generator r, .refl _⟩
  | _, _, .wiring w => ⟨.wiring w, .refl _⟩
  | _, _, .seq f g =>
      let nf := normalizeWithPath f
      let ng := normalizeWithPath g
      let d := Diagram.seq nf.1 ng.1
      ⟨normalizeTop d, .comp (.comp (nf.2.seqLeft g) (Cell3.seqRight nf.1 ng.2))
        (normalizeTopPath d)⟩
  | _, _, .tensor f g =>
      let nf := normalizeWithPath f
      let ng := normalizeWithPath g
      ⟨.tensor nf.1 ng.1, .comp (nf.2.tensorLeft g) (Cell3.tensorRight nf.1 ng.2)⟩
  | _, _, .tuple f =>
      ⟨.tuple (fun i => (normalizeWithPath (f i)).1),
        Cell3.tuple (fun i => (normalizeWithPath (f i)).2)⟩

def normalize {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) : Diagram T Γ Δ :=
  (normalizeWithPath d).1

def normalizePath {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) : Cell3 d (normalize d) :=
  (normalizeWithPath d).2

@[simp] theorem normalize_forest {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    (normalize d).toForest = d.toForest := (normalizePath d).forest_eq.symm

end Foundation.Logic.Polygraph.Diagram
