import Foundation.Quantum.NuclearNorm

/-! Bounded ideal operations for the representation-independent nuclear norm. -/
namespace Foundation.Quantum.Infinite.TraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem norm_post_le (T : TraceClass E) (A : E →L[ℂ] E) : ‖T.post A‖ ≤ ‖A‖ * ‖T‖ := by
  apply nuclearNorm_transfer_le T (T.post A) ‖A‖ (norm_nonneg A)
  intro S hS
  refine ⟨S.post A, ?_, S.mass_post_le A⟩
  rw [NuclearSeries.post_operator, hS]
  rfl

theorem norm_pre_le (T : TraceClass E) (A : E →L[ℂ] E) : ‖T.pre A‖ ≤ ‖A‖ * ‖T‖ := by
  apply nuclearNorm_transfer_le T (T.pre A) ‖A‖ (norm_nonneg A)
  intro S hS
  refine ⟨S.pre A, ?_, S.mass_pre_le A⟩
  rw [NuclearSeries.pre_operator, hS]
  rfl

theorem norm_conjugate_le (T : TraceClass E) (A : E →L[ℂ] F) :
    ‖T.conjugate A‖ ≤ ‖A‖ ^ 2 * ‖T‖ := by
  apply nuclearNorm_transfer_le T (T.conjugate A) (‖A‖^2) (sq_nonneg _)
  intro S hS
  refine ⟨(S.post A).pre A.adjoint, ?_, ?_⟩
  · rw [NuclearSeries.pre_operator, NuclearSeries.post_operator, hS]
    rfl
  · have h := (S.post A).mass_pre_le A.adjoint
    rw [ContinuousLinearMap.adjoint.norm_map] at h
    have hp := mul_le_mul_of_nonneg_left (S.mass_post_le A) (norm_nonneg A)
    nlinarith

/-- The conjugation operation is continuous between the actual normed ideals. -/
def conjugateContinuous (A : E →L[ℂ] F) : TraceClass E →L[ℂ] TraceClass F :=
  (show TraceClass E →ₗ[ℂ] TraceClass F from
    { toFun := fun T => T.conjugate A
      map_add' := fun S T => by
        apply TraceClass.ext
        simp [conjugate, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      map_smul' := fun c T => by
        apply TraceClass.ext
        simp [conjugate, ContinuousLinearMap.smul_comp] }).mkContinuous
    (‖A‖^2) (fun T => T.norm_conjugate_le A)

end
end Foundation.Quantum.Infinite.TraceClass
