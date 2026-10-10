import Foundation.Quantum.Hilbert
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Infinite-dimensional Hilbert predicates require closures and continuous
maps. No infinite-dimensional cup or arbitrary unbounded adjoint is asserted. -/
namespace Foundation.Quantum.Infinite
noncomputable section
local instance {X : Type*} : DecidableEq X := Classical.decEq X
open scoped InnerProductSpace
open Topology Filter
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev Pred (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := ClosedSubmodule ℂ E

omit [CompleteSpace E] [CompleteSpace F] in
/-- Existential transport takes the closure of the image; raw image need not be closed. -/
theorem exists_pull (f : E →L[ℂ] F) (P : Pred E) (Q : Pred F) :
    P.map f ≤ Q ↔ P ≤ Q.comap f := ClosedSubmodule.map_le_iff_le_comap

theorem double_orthogonal (P : Submodule ℂ E) : Pᗮᗮ = P.topologicalClosure :=
  P.orthogonal_orthogonal_eq_closure

theorem kernel_adjoint (f : E →L[ℂ] F) :
    f.kerᗮ = f.adjoint.range.topologicalClosure := f.orthogonal_ker

theorem range_adjoint (f : E →L[ℂ] F) : f.rangeᗮ = f.adjoint.ker := f.orthogonal_range

omit [CompleteSpace E] in
/-- Directed finite observations converge in norm, rather than becoming an infinite proof tree. -/
theorem finite_projection_limit {ι : Type*} (b : HilbertBasis ι ℂ E) (x : E) :
    Tendsto (fun J : Finset ι =>
      (Submodule.span ℂ (J.image b : Set E)).starProjection x) atTop (𝓝 x) := by
  classical
  have hm : Monotone (fun J : Finset ι => Submodule.span ℂ (J.image b : Set E)) := by
    intro J K h
    exact Submodule.span_mono (by
      intro v hv
      exact Finset.mem_image.mpr (by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨i, h hi, rfl⟩))
  exact Submodule.starProjection_tendsto_self _ hm x (by rw [b.finite_spans_dense])

/-- A genuine countably infinite Hilbert space; no finite-dimensional instance is required. -/
abbrev SequenceSpace := lp (fun _ : ℕ => ℂ) 2

/-- The finite-observation approximation theorem applies to this infinite space. -/
theorem sequence_space_approximation (x : SequenceSpace) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ SequenceSpace),
      Tendsto (fun J : Finset ι =>
        (Submodule.span ℂ (J.image b : Set SequenceSpace)).starProjection x) atTop (𝓝 x) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ SequenceSpace
  refine ⟨ι, b, ?_⟩
  simpa only [Finset.coe_image] using finite_projection_limit b x

end
end Foundation.Quantum.Infinite
