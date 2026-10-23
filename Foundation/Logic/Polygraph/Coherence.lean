import Foundation.Logic.Polygraph.Higher
import Foundation.Logic.Polygraph.Normalization
import Foundation.Logic.Polygraph.Structural

/-! Normalizing four-dimensional completions. A fiber retains all expressions
and all rewrites with a fixed formal normal form. It does not identify rules
having different normal forms. The square schema is generally infinite. -/
namespace Foundation.Logic.Polygraph

universe u v w

structure Normalizer {A : Type u} (R : A → A → Type v) where
  Key : Type w
  key : A → Key
  preserves : ∀ {a b}, R a b → key a = key b
  representative : Key → A
  key_representative : ∀ k, key (representative k) = k
  path : ∀ a, RewritePath R a (representative (key a))

namespace Normalizer
variable {A : Type u} {R : A → A → Type v} (N : Normalizer.{u, v, w} R)

abbrev Vertex (k : N.Key) := {a : A // N.key a = k}
abbrev Step (k : N.Key) (a b : N.Vertex k) := R a.val b.val

theorem path_key {a b : A} (p : RewritePath R a b) : N.key a = N.key b := by
  induction p with
  | refl => rfl
  | cons s p ih => exact (N.preserves s).trans ih

def liftPath {k : N.Key} : {a b : A} → (p : RewritePath R a b) →
    (ha : N.key a = k) → RewritePath (N.Step k)
      ⟨a, ha⟩ ⟨b, (N.path_key p).symm.trans ha⟩
  | _, _, .refl _, _ => .refl _
  | _, _, .cons (b := b) s p, ha =>
      .cons (b := (⟨b, (N.preserves s).symm.trans ha⟩ : N.Vertex k)) s
        (liftPath p ((N.preserves s).symm.trans ha))

def target (k : N.Key) : N.Vertex k := ⟨N.representative k, N.key_representative k⟩

def normal (k : N.Key) (a : N.Vertex k) : Track (N.Step k) a (N.target k) := by
  have p := N.liftPath (N.path a.val) a.property
  have he : (⟨N.representative (N.key a.val), (N.path_key (N.path a.val)).symm.trans
      a.property⟩ : N.Vertex k) = N.target k :=
    Subtype.ext (congrArg N.representative a.property)
  exact he ▸ Track.ofPath p

abbrev Cell4 {k : N.Key} {a b : N.Vertex k} (p q : Track (N.Step k) a b) :=
  Four (NormalSquare (N.target k) (N.normal k)) p q

/-- An actual composite four-cell, built by recursion on the two paths. -/
def coherent {k : N.Key} {a b : N.Vertex k} (p q : Track (N.Step k) a b) :
    N.Cell4 p q := NormalSquare.coherent (N.normal k) p q

end Normalizer

namespace Composition.Expr
variable {O : Type u} {E : O → O → Type v} (a b : O)

def normalizer : Normalizer (@Step O E a b) where
  Key := Chain E a b
  key := flatten
  preserves := Step.flatten_eq
  representative := Chain.reflect
  key_representative := flatten_reflect
  path := normalizePath

end Composition.Expr

namespace Diagram
universe j r
variable {T : Presentation.{j, r}} (Γ Δ : Logic.Context T)

/-- The whole cartesian syntax has a normalizing completion via term
reconstruction. Its rewrite relation is not claimed to terminate. -/
def normalizer : Normalizer (@StructuralStep T Γ Δ) where
  Key := Forest Γ Δ
  key := toForest
  preserves := StructuralStep.forest_eq
  representative := ofForest
  key_representative := toForest_ofForest
  path := fun d => .single (.reconstruct d)

end Diagram
end Foundation.Logic.Polygraph
