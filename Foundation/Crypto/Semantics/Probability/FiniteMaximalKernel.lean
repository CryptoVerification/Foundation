import Foundation.Crypto.Semantics.Probability.FiniteMaximalCoupling

/-! Conditional kernels for the finite maximal joint law, including an
explicit fallback on unreachable input values. -/
namespace Foundation.Probability.FiniteMaximalCoupling
open scoped BigOperators ENNReal
noncomputable section
variable {α : Type} [Fintype α] (p q : PMF α)

theorem mass_zero_of_left_zero (x y : α) (h : (p x).toReal = 0) : mass p q x y = 0 := by
  have hb : mass p q x y ≤ ∑ z, mass p q x z :=
    Finset.single_le_sum (fun z _ => mass_nonneg p q x z) (Finset.mem_univ y)
  rw [row_sum, h] at hb
  exact le_antisymm hb (mass_nonneg p q x y)

def kernel (x : α) : PMF α :=
  if h : (p x).toReal = 0 then q else PMF.ofFintype
    (fun y => ENNReal.ofReal (mass p q x y / (p x).toReal)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => div_nonneg (mass_nonneg p q x y) ENNReal.toReal_nonneg),
        ← Finset.sum_div, row_sum, div_self h]
      simp)

theorem weighted_kernel (x y : α) : p x * kernel p q x y = joint p q (x,y) := by
  classical
  by_cases h : (p x).toReal = 0
  · have hp : p x = 0 := (ENNReal.toReal_eq_zero_iff (p x)).mp h |>.resolve_right (p.apply_ne_top x)
    change p x * kernel p q x y = ENNReal.ofReal (mass p q x y)
    rw [hp, zero_mul, mass_zero_of_left_zero p q x y h, ENNReal.ofReal_zero]
  · apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top (p.apply_ne_top x) ((kernel p q x).apply_ne_top y))
      ((joint p q).apply_ne_top (x,y))).mp
    rw [ENNReal.toReal_mul, joint_real]
    simp only [kernel, dif_neg h, PMF.ofFintype_apply,
      ENNReal.toReal_ofReal (div_nonneg (mass_nonneg p q x y) ENNReal.toReal_nonneg)]
    field_simp

theorem kernel_joint : (p.bind fun x => (kernel p q x).map fun y => (x,y)) = joint p q := by
  classical
  ext pair
  rcases pair with ⟨x,y⟩
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk.injEq, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, mul_ite, mul_zero]
  exact weighted_kernel p q x y

theorem kernel_preserve : p.bind (kernel p q) = q := by
  have h := congrArg (fun law => law.map Prod.snd) (kernel_joint p q)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, joint_right] at h
  change (p.bind fun x => (kernel p q x).map id) = q at h
  simpa only [PMF.map_id] using h

end
end Foundation.Probability.FiniteMaximalCoupling
