import Foundation.Quantum.QKD.CommonKeyProcessing

/-! Mixtures of accepted branches retain their original weights. In
particular acceptance is not normalized separately inside each public choice. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {S X : Type} [Fintype S] [Fintype X] {e : Space}

def mixture (p : PMF S) (ρ : S → State X e) : State X e where
  block x := ∑ s, ((p s).toReal:ℂ) • (ρ s).block x
  positive x := Matrix.posSemidef_sum _ (fun s _ => ((ρ s).positive x).smul
    (Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg,by simp⟩))
  bounded := by
    simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Finset.sum_comm]
    calc
      _ = ∑ s, (p s).toReal * mass (ρ s) := by simp only [mass, Finset.mul_sum]
      _ ≤ ∑ s, (p s).toReal * 1 := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (ρ s).bounded ENNReal.toReal_nonneg)
      _ = 1 := by simp only [mul_one, Density.probability_weights]

theorem joint_mixture [DecidableEq X] (p : PMF S) (ρ : S → State X e) :
    joint (mixture p ρ) = ∑ s, ((p s).toReal:ℂ) • joint (ρ s) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective i
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective j
  rw [joint_block]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hj (s : S) := joint_block (ρ s) x y u v
  simp_rw [hj]
  by_cases h : x = y
  · simp only [h, ite_true, mixture, Matrix.sum_apply, Matrix.smul_apply]
  · simp [h]

theorem mixture_approx [DecidableEq X] (p : PMF S) (ρ σ : S → State X e) (ε : S → ℝ)
    (h : ∀ s, OperatorApprox (joint (ρ s)) (joint (σ s)) (ε s)) :
    OperatorApprox (joint (mixture p ρ)) (joint (mixture p σ)) (∑ s, (p s).toReal * ε s) := by
  rw [joint_mixture, joint_mixture]
  intro E
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ s, |(p s).toReal * ((E.matrix * joint (ρ s)).trace.re -
        (E.matrix * joint (σ s)).trace.re)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, (p s).toReal * |(E.matrix * joint (ρ s)).trace.re -
        (E.matrix * joint (σ s)).trace.re| := by
      simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s E) ENNReal.toReal_nonneg)

end
end Foundation.Quantum.QKD.Subnormalized
