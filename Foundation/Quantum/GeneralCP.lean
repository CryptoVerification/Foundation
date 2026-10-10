import Foundation.Logic.Presentation
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-! Dimension-independent completely positive maps, with their finite
matrix amplification condition. Normality and preduals are separate obligations. -/
namespace Foundation.Quantum.GeneralCP
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped CStarAlgebra

variable {A B C : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def identity (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    A →CP A where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' _ M h := by simpa using h

def comp (g : B →CP C) (f : A →CP B) : A →CP C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_cstarMatrix_nonneg' k M h := by
    have h' := g.map_cstarMatrix_nonneg (M.map f) (f.map_cstarMatrix_nonneg M h)
    have he : (M.map f).map g = M.map (g.toLinearMap.comp f.toLinearMap) := by
      ext i j
      rfl
    rw [he] at h'
    exact h'

@[simp] theorem comp_apply (g : B →CP C) (f : A →CP B) (x : A) : comp g f x = g (f x) := rfl

/-- This holds for every finite matrix level, with no finite-dimensional assumption on A or B. -/
theorem amplification_positive (f : A →CP B) {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) (h : 0 ≤ M) : 0 ≤ M.map f := f.map_cstarMatrix_nonneg M h

/-- Every actual star algebra homomorphism supplies a verified CP map. -/
def ofHom (f : A →⋆ₙₐ[ℂ] B) : A →CP B := f

@[simp] theorem ofHom_apply (f : A →⋆ₙₐ[ℂ] B) (x : A) : ofHom f x = f x := rfl

/-- Local operator equality is preserved by a general CP operation. -/
theorem congruent (f : A →CP B) {x y : A} (h : x = y) : f x = f y := congrArg f h

end
end Foundation.Quantum.GeneralCP
