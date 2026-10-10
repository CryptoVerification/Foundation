import Foundation.Quantum.ClassicalComposition
import Foundation.Quantum.PublicMixtureObservation
import Foundation.Quantum.QKD.SubnormalizedRelabel

/-! A coupling bound for two classical processings of the same positive
quantum blocks. Arbitrary joint effects are allowed; conditional quantum
states are not replaced by scalar distributions. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {e : Space}

/-- A binary effect on a positive, possibly subnormalized block lies between
zero and that block's actual trace. -/
theorem trace_effect_bounds (E : Effect e) (B : Operator e) (hB : B.PosSemidef) :
    0 ≤ (E.matrix*B).trace.re ∧ (E.matrix*B).trace.re ≤ B.trace.re := by
  constructor
  · exact (Complex.nonneg_iff.mp (trace_product_nonneg E.positive hB)).1
  · have h := (Complex.nonneg_iff.mp (trace_product_nonneg E.complement_positive hB)).1
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h
    linarith

theorem joint_event_observation [DecidableEq X] (ρ : State X e)
    (P : X → Prop) [DecidablePred P] :
    ((recordEvent e (fun r => P ((Fintype.equivFin X).symm r))).matrix * joint ρ).trace.re =
      ∑ x, if P x then (ρ.block x).trace.re else 0 := by
  change (Matrix.diagonal _ * joint ρ).trace.re = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Fintype.sum_prod_type]
  rw [← (Fintype.equivFin X).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [joint_block ρ]
  simp only [ite_true]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> simp [hp]

theorem relabel_event_observation [DecidableEq Y] (ρ : State X e) (f : X → Y)
    (P : Y → Prop) [DecidablePred P] :
    ((recordEvent e (fun r => P ((Fintype.equivFin Y).symm r))).matrix * joint (relabel ρ f)).trace.re =
      ∑ x, if P (f x) then (ρ.block x).trace.re else 0 := by
  rw [joint_event_observation (relabel ρ f) P]
  simp only [relabel, Matrix.trace_sum, Complex.re_sum, apply_ite, Matrix.trace_zero, Complex.zero_re]
  have hd (y : Y) :
      (if P y then ∑ x, if f x = y then (ρ.block x).trace.re else 0 else 0) =
        ∑ x, if f x = y then (if P y then (ρ.block x).trace.re else 0) else 0 := by
    by_cases hy : P y <;> simp [hy]
  simp_rw [hd]
  rw [Finset.sum_comm]
  simp

theorem relabel_observation [DecidableEq Y] (ρ : State X e) (f : X → Y)
    (E : Effect (Guessing.publicSpace Y e)) :
    (E.matrix*joint (relabel ρ f)).trace.re = ∑ x, ((E.readPublic (f x)).matrix*ρ.block x).trace.re := by
  unfold joint
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  have ht (y : Y) := Guessing.trace_classical_block E.matrix y ((relabel ρ f).block y)
  simp_rw [ht]
  simp only [relabel, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [apply_ite, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  simp [Effect.readPublic]

/-- Disagreement is weighted by the original block mass, not by a posterior
conditional probability after accepting a branch. -/
def disagreement [DecidableEq Y] (ρ : State X e) (f g : X → Y) : ℝ :=
  ∑ x, if f x = g x then 0 else (ρ.block x).trace.re

theorem relabel_coupling [DecidableEq Y] (ρ : State X e) (f g : X → Y) :
    OperatorApprox (joint (relabel ρ f)) (joint (relabel ρ g)) (disagreement ρ f g) := by
  intro E
  rw [relabel_observation, relabel_observation, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : f x = g x
  · simp [hx]
  · simp only [hx, ite_false]
    have hf := trace_effect_bounds (E.readPublic (f x)) (ρ.block x) (ρ.positive x)
    have hg := trace_effect_bounds (E.readPublic (g x)) (ρ.block x) (ρ.positive x)
    apply abs_le.mpr
    constructor <;> linarith

theorem joint_injective [DecidableEq X] {ρ σ : State X e} (h : joint ρ = joint σ) : ρ = σ := by
  apply State.ext
  funext x
  ext i j
  have hh := congrFun (congrFun h (Fintype.equivFin X x,i)) (Fintype.equivFin X x,j)
  rw [joint_block ρ x x i j, joint_block σ x x i j] at hh
  simpa only [ite_true] using hh

theorem relabel_id [DecidableEq X] (ρ : State X e) : relabel ρ id = ρ := by
  apply State.ext
  funext x
  simp [relabel]

theorem relabel_comp [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (ρ : State X e) (f : X → Y) (g : Y → Z) :
    relabel (relabel ρ f) g = relabel ρ (g ∘ f) := by
  apply joint_injective
  rw [relabel_physical, relabel_physical, classicalMap_compose, relabel_physical]
  have hf : ((fun t => Fintype.equivFin Z (g ((Fintype.equivFin Y).symm t))) ∘
      (fun t => Fintype.equivFin Y (f ((Fintype.equivFin X).symm t)))) =
        (fun t => Fintype.equivFin Z ((g ∘ f) ((Fintype.equivFin X).symm t))) := by
    funext r
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hf]

end
end Foundation.Quantum.QKD.Subnormalized
