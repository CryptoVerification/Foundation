import Foundation.Quantum.TraceClass
import Foundation.Quantum.NuclearAlgebra
import Mathlib.Algebra.Module.TransferInstance

/-! Trace-class operators form an actual complex linear space and a two-sided
ideal under bounded pre- and postcomposition. The trace is complex-linear. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Closure properties refer to actual operators. -/
def nuclearSubmodule : Submodule ℂ (E →L[ℂ] E) where
  carrier T := ∃ S : NuclearSeries E E, S.operator = T
  zero_mem' := ⟨NuclearSeries.single 0 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨S.add T, S.add_operator T⟩
  smul_mem' := by
    rintro c _ ⟨S, rfl⟩
    exact ⟨S.scale c, S.scale_operator c⟩

namespace TraceClass

def equivSubmodule : TraceClass E ≃ nuclearSubmodule (E := E) where
  toFun T := ⟨T.operator, T.representable⟩
  invFun T := ⟨T.val, T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TraceClass E) := equivSubmodule.addCommGroup
instance : Module ℂ (TraceClass E) := Equiv.module ℂ equivSubmodule

omit [CompleteSpace E] in
@[ext] theorem ext {S T : TraceClass E} (h : S.operator = T.operator) : S = T := by
  cases S
  cases T
  cases h
  rfl

@[simp] theorem operator_zero : (0 : TraceClass E).operator = 0 := rfl
@[simp] theorem operator_add (S T : TraceClass E) : (S + T).operator = S.operator + T.operator := rfl
@[simp] theorem operator_smul (c : ℂ) (T : TraceClass E) : (c • T).operator = c • T.operator := rfl
@[simp] theorem operator_neg (T : TraceClass E) : (-T).operator = -T.operator := rfl

/-- The embedding into bounded operators is a faithful linear map. -/
def inclusion : TraceClass E →ₗ[ℂ] E →L[ℂ] E where
  toFun := operator
  map_add' := operator_add
  map_smul' := operator_smul

@[simp] theorem trace_zero : (0 : TraceClass E).trace = 0 := by
  have he : (0 : TraceClass E) = ofSeries (NuclearSeries.single 0 0) := by ext; simp [ofSeries]
  rw [he, trace_ofSeries, NuclearSeries.single_traceExpression]
  simp

@[simp] theorem trace_add (S T : TraceClass E) : (S + T).trace = S.trace + T.trace := by
  let X := S.representable.choose
  let Y := T.representable.choose
  have hX : X.operator = S.operator := S.representable.choose_spec
  have hY : Y.operator = T.operator := T.representable.choose_spec
  have hXY : (S + T).operator = (ofSeries (X.add Y)).operator := by
    simp only [operator_add, ofSeries, NuclearSeries.add_operator, hX, hY]
  rw [trace_congr _ _ hXY, trace_ofSeries, NuclearSeries.add_trace]
  rfl

@[simp] theorem trace_smul (c : ℂ) (T : TraceClass E) : (c • T).trace = c * T.trace := by
  let S := T.representable.choose
  have hS : S.operator = T.operator := T.representable.choose_spec
  have he : (c • T).operator = (ofSeries (S.scale c)).operator := by
    simp only [operator_smul, ofSeries, NuclearSeries.scale_operator, hS]
  rw [trace_congr _ _ he, trace_ofSeries, NuclearSeries.scale_trace]
  rfl

def traceLinear : TraceClass E →ₗ[ℂ] ℂ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

/-- Left multiplication by a bounded operator preserves the ideal. -/
def post (T : TraceClass E) (A : E →L[ℂ] E) : TraceClass E where
  operator := A.comp T.operator
  representable := ⟨T.representable.choose.post A, by
    rw [NuclearSeries.post_operator, T.representable.choose_spec]⟩

/-- Right multiplication by a bounded operator preserves the ideal. -/
def pre (T : TraceClass E) (A : E →L[ℂ] E) : TraceClass E where
  operator := T.operator.comp A
  representable := ⟨T.representable.choose.pre A, by
    rw [NuclearSeries.pre_operator, T.representable.choose_spec]⟩

theorem trace_cyclic (T : TraceClass E) (A : E →L[ℂ] E) : (T.post A).trace = (T.pre A).trace := by
  let S := T.representable.choose
  have hS : S.operator = T.operator := T.representable.choose_spec
  have hp : (T.post A).operator = (ofSeries (S.post A)).operator := by
    simp only [post, ofSeries, NuclearSeries.post_operator, hS]
  have hq : (T.pre A).operator = (ofSeries (S.pre A)).operator := by
    simp only [pre, ofSeries, NuclearSeries.pre_operator, hS]
  rw [trace_congr _ _ hp, trace_congr _ _ hq, trace_ofSeries, trace_ofSeries]
  exact S.trace_cyclic A

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded operator transports a nuclear state between different Hilbert spaces. -/
def conjugate (T : TraceClass E) (A : E →L[ℂ] F) : TraceClass F where
  operator := (A.comp T.operator).comp A.adjoint
  representable := ⟨(T.representable.choose.post A).pre A.adjoint, by
    rw [NuclearSeries.pre_operator, NuclearSeries.post_operator,
      T.representable.choose_spec]⟩

theorem trace_conjugate (T : TraceClass E) (A : E →L[ℂ] F) :
    (T.conjugate A).trace = (T.post (A.adjoint.comp A)).trace := by
  let S := T.representable.choose
  have hS : S.operator = T.operator := T.representable.choose_spec
  have hc : (T.conjugate A).operator = (ofSeries ((S.post A).pre A.adjoint)).operator := by
    simp only [conjugate, ofSeries, NuclearSeries.pre_operator,
      NuclearSeries.post_operator, hS]
  have hp : (T.post (A.adjoint.comp A)).operator =
      (ofSeries (S.post (A.adjoint.comp A))).operator := by
    simp only [post, ofSeries, NuclearSeries.post_operator, hS]
  rw [trace_congr _ _ hc, trace_congr _ _ hp, trace_ofSeries, trace_ofSeries]
  apply tsum_congr
  intro n
  simp only [NuclearSeries.pre, NuclearSeries.post, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact (A.adjoint_inner_right (S.right n) (A (S.left n))).symm

theorem conjugate_positive (T : TraceClass E) (h : T.operator.IsPositive)
    (A : E →L[ℂ] F) : (T.conjugate A).operator.IsPositive := by
  exact h.conj_adjoint A

theorem trace_conjugate_isometry (T : TraceClass E) (A : E →L[ℂ] F)
    (hA : A.adjoint.comp A = ContinuousLinearMap.id ℂ E) :
    (T.conjugate A).trace = T.trace := by
  rw [trace_conjugate, hA]
  apply trace_congr
  simp only [post, ContinuousLinearMap.id_comp]

end TraceClass

/-- Isometric evolution preserves positivity and trace on arbitrary Hilbert spaces. -/
def TraceDensity.runIsometry {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (ρ : TraceDensity E)
    (A : E →L[ℂ] F) (hA : A.adjoint.comp A = ContinuousLinearMap.id ℂ E) : TraceDensity F where
  state := ρ.state.conjugate A
  positive := ρ.state.conjugate_positive ρ.positive A
  normalized := (ρ.state.trace_conjugate_isometry A hA).trans ρ.normalized

end
end Foundation.Quantum.Infinite
