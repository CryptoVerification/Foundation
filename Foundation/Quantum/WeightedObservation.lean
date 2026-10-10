import Foundation.Quantum.TraceCauchy
import Foundation.Quantum.QKD.CollisionVariance

/-! Weighted binary-observation bounds without commutation assumptions.
A reconstruction factorization is explicit; invertibility is not assumed.
Its construction from a reference density/support is a separate obligation. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

/-- A positive interval gives the sharp half-centered trace-square bound. -/
theorem trace_interval_contrast {e : Space} (A M : Operator e)
    (hA : A.PosSemidef) (hMA : (M-A).PosSemidef) :
    ((A - (1/2:ℂ) • M) * (A - (1/2:ℂ) • M)).trace.re ≤ (1/4:ℝ)*(M*M).trace.re := by
  have h := (Complex.nonneg_iff.mp (trace_product_nonneg hA hMA)).1
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  have hc := QKD.Collision.trace_center A M (1/2)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
  rw [Matrix.trace_mul_comm M A] at hc
  linarith

/-- Every effect stays in the interval [0,D D†] under conjugation. -/
theorem weighted_effect_contrast {e : Space} (D : Operator e) (E : Effect e) :
    (((D*E.matrix*D.conjTranspose) - (1/2:ℂ) • (D*D.conjTranspose)) *
      ((D*E.matrix*D.conjTranspose) - (1/2:ℂ) • (D*D.conjTranspose))).trace.re ≤
        (1/4:ℝ)*((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re := by
  apply trace_interval_contrast _ _ (E.positive.mul_mul_conjTranspose_same D)
  have hp := E.complement_positive.mul_mul_conjTranspose_same D
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] using hp

/-- For a trace-zero difference reconstructed as D† C D, every physical
binary observation is bounded by one half of the weighted collision root. -/
theorem weighted_observation {e : Space} (Δ C D : Operator e)
    (hC : C.IsHermitian) (hrec : Δ = D.conjTranspose*C*D) (hzero : Δ.trace = 0)
    (E : Effect e) :
    |(E.matrix*Δ).trace.re| ≤ (1/2:ℝ) * Real.sqrt
      (((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re * (C*C).trace.re) := by
  let A := D*E.matrix*D.conjTranspose
  let M := D*D.conjTranspose
  let T := A - (1/2:ℂ) • M
  have hA : A.PosSemidef := E.positive.mul_mul_conjTranspose_same D
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose D
  have hT : T.IsHermitian := hA.isHermitian.sub
    (hM.smul (by apply Complex.nonneg_iff.mpr; norm_num : (0:ℂ) ≤ 1/2)).isHermitian
  have hMC : (M*C).trace = 0 := by
    calc
      _ = (D.conjTranspose*C*D).trace := by
        simpa only [M, Matrix.mul_assoc] using Matrix.trace_mul_comm D (D.conjTranspose*C)
      _ = 0 := hrec ▸ hzero
  have hobs : (E.matrix*Δ).trace = (A*C).trace := by
    rw [hrec]
    simpa only [A, Matrix.mul_assoc] using Matrix.trace_mul_cycle (E.matrix*D.conjTranspose) C D
  have hcenter : (T*C).trace = (E.matrix*Δ).trace := by
    rw [hobs]
    simp only [T, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      hMC, smul_zero, sub_zero]
  have hc := trace_cauchy T C hT hC
  have ht := weighted_effect_contrast D E
  change (T*T).trace.re ≤ (1/4:ℝ)*(M*M).trace.re at ht
  have hcp := trace_square_nonneg C hC
  have hmp := trace_square_nonneg M hM.isHermitian
  have hr := Real.sq_sqrt (mul_nonneg hmp hcp)
  have hn := Real.sqrt_nonneg ((M*M).trace.re*(C*C).trace.re)
  rw [hcenter] at hc
  have hp := mul_le_mul_of_nonneg_right ht hcp
  nlinarith [sq_abs ((E.matrix*Δ).trace.re), abs_nonneg ((E.matrix*Δ).trace.re)]

end
end Foundation.Quantum
