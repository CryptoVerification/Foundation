import Foundation.Quantum.TraceAlgebra

/-! Finite Kraus operations on arbitrary complete complex Hilbert spaces.
These are concrete operations on trace-class states, not a classification of
all normal CP maps. No finite-dimensional assumption on the Hilbert spaces. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

structure HilbertChannel (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] where
  index : Type
  finite : Fintype index
  operator : index → E →L[ℂ] F
  complete : letI := finite; ∑ i, (operator i).adjoint.comp (operator i) =
    ContinuousLinearMap.id ℂ E

namespace HilbertChannel
attribute [instance] finite

def apply (K : HilbertChannel E F) (T : TraceClass E) : TraceClass F :=
  ∑ i, T.conjugate (K.operator i)

theorem operator_apply (K : HilbertChannel E F) (T : TraceClass E) :
    (K.apply T).operator = ∑ i, ((K.operator i).comp T.operator).comp (K.operator i).adjoint := by
  exact (map_sum TraceClass.inclusion _ _)

theorem positive_apply (K : HilbertChannel E F) (T : TraceClass E)
    (h : T.operator.IsPositive) : (K.apply T).operator.IsPositive := by
  rw [operator_apply]
  exact ContinuousLinearMap.isPositive_sum _ (fun i _ => h.conj_adjoint (K.operator i))

theorem trace_apply (K : HilbertChannel E F) (T : TraceClass E) :
    (K.apply T).trace = T.trace := by
  change TraceClass.traceLinear (∑ i, T.conjugate (K.operator i)) = _
  rw [map_sum]
  simp only [TraceClass.traceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    TraceClass.trace_conjugate]
  let effectAction : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E :=
    { toFun := fun A => A.comp T.operator
      map_add' := fun _ _ => ContinuousLinearMap.add_comp _ _ _
      map_smul' := fun _ _ => ContinuousLinearMap.smul_comp _ _ _ }
  have he : (∑ i, T.post ((K.operator i).adjoint.comp (K.operator i))).operator = T.operator := by
    change TraceClass.inclusion (∑ i, T.post ((K.operator i).adjoint.comp (K.operator i))) = _
    rw [map_sum]
    change (∑ i, effectAction ((K.operator i).adjoint.comp (K.operator i))) = _
    rw [← map_sum, K.complete]
    exact ContinuousLinearMap.id_comp _
  have ht := TraceClass.trace_congr _ T he
  change TraceClass.traceLinear (∑ i, T.post ((K.operator i).adjoint.comp (K.operator i))) = _ at ht
  rw [map_sum] at ht
  exact ht

def run (K : HilbertChannel E F) (ρ : TraceDensity E) : TraceDensity F where
  state := K.apply ρ.state
  positive := K.positive_apply ρ.state ρ.positive
  normalized := (K.trace_apply ρ.state).trans ρ.normalized

def identity (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    HilbertChannel E E where
  index := Unit
  finite := inferInstance
  operator _ := ContinuousLinearMap.id ℂ E
  complete := by simp

@[simp] theorem identity_apply (T : TraceClass E) : (identity E).apply T = T := by
  apply TraceClass.ext
  simp [operator_apply, identity]

end HilbertChannel
end
end Foundation.Quantum.Infinite
