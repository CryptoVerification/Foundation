import Foundation.Quantum.QKD.CoherentSupport
import Foundation.Quantum.OperatorDistance

/-! Sharp pure-state projection estimate on an explicitly constructed
orthonormal two-dimensional span. The proof uses the actual positive span
projector and the existing weighted observation theorem, not a trace-distance
axiom or a dimension-dependent Hilbert--Schmidt estimate. -/
namespace Foundation.Quantum.PureProjection
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

def bracket (u v : e.Basis → ℂ) : ℂ := ∑ i, star (u i) * v i
def rank (u v : e.Basis → ℂ) : Operator e := Matrix.vecMulVec u (star v)

@[simp] theorem rank_trace (u v : e.Basis → ℂ) : (rank u v).trace = bracket v u := by
  simp only [rank, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, bracket, mul_comm]

@[simp] theorem rank_adjoint (u v : e.Basis → ℂ) : (rank u v).conjTranspose = rank v u := by
  ext i j
  simp [rank, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

theorem rank_mul (u v w z : e.Basis → ℂ) : rank u v * rank w z = bracket v w • rank u z := by
  ext i j
  simp only [rank, bracket, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

@[simp] theorem bracket_add_left (u v w : e.Basis → ℂ) : bracket (u+v) w = bracket u w + bracket v w := by
  simp [bracket, star_add, add_mul, Finset.sum_add_distrib]
@[simp] theorem bracket_add_right (u v w : e.Basis → ℂ) : bracket u (v+w) = bracket u v + bracket u w := by
  simp [bracket, mul_add, Finset.sum_add_distrib]
@[simp] theorem bracket_smul_left (c : ℂ) (u v : e.Basis → ℂ) : bracket (c • u) v = star c * bracket u v := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
@[simp] theorem bracket_smul_right (c : ℂ) (u v : e.Basis → ℂ) : bracket u (c • v) = c * bracket u v := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Rank-one input densities are normalized by their actual vector norm. -/
def pure (u : e.Basis → ℂ) (hu : bracket u u = 1) : Density e where
  matrix := rank u u
  positive := QKD.CoherentSupport.outer_positive u
  normalized := (rank_trace u u).trans hu

/-- On two orthonormal directions, discarding the bad amplitude costs exactly
its modulus as an upper bound for every binary quantum observation. -/
theorem orthogonal_projection (u w : e.Basis → ℂ) (a b : ℂ)
    (hu : bracket u u = 1) (hw : bracket w w = 1)
    (huw : bracket u w = 0) (hwu : bracket w u = 0)
    (hab : a*star a + b*star b = 1) :
    OperatorApprox (rank (a • u+b • w) (a • u+b • w)) (rank u u)
      (Real.sqrt (b*star b).re) := by
  let v := a • u+b • w
  let P := rank u u+rank w w
  let Δ := rank v v-rank u u
  have hv : bracket v v = 1 := by
    simp only [v, bracket_add_left, bracket_add_right, bracket_smul_left, bracket_smul_right,
      hu, hw, huw, hwu, mul_zero, mul_one, zero_add, add_zero]
    linear_combination hab
  have huv : bracket u v = a := by simp [v, hu, huw]
  have hwu' : bracket w v = b := by simp [v, hw, hwu]
  have hvu : bracket v u = star a := by simp [v, hu, hwu]
  have hvw : bracket v w = star b := by simp [v, hw, huw]
  have hP : P.conjTranspose = P := by simp [P]
  have hΔ : Δ.conjTranspose = Δ := by simp [Δ]
  have hPP : P*P = P := by
    simp [P, Matrix.add_mul, Matrix.mul_add, rank_mul, hu, hw, huw, hwu]
  have hvspan : P*rank v v = rank v v := by
    simp only [P, Matrix.add_mul, rank_mul, huv, hwu']
    ext i j
    simp only [rank, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have huspan : P*rank u u = rank u u := by
    simp [P, Matrix.add_mul, rank_mul, hu, hwu]
  have hleft : P*Δ = Δ := by
    dsimp only [Δ]
    rw [Matrix.mul_sub, hvspan, huspan]
  have hright : Δ*P = Δ := by
    have hh := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, hP, hΔ] using hh
  have hrec : Δ = P.conjTranspose*Δ*P := by rw [hP, hleft, hright]
  have htrace : (rank v v).trace = (rank u u).trace := by simp [hv, hu]
  have hcost : ((P*P.conjTranspose)*(P*P.conjTranspose)).trace.re = 2 := by
    rw [hP, hPP, hPP]
    norm_num [P, Matrix.trace_add, hu, hw]
  have hsquare : (Δ*Δ).trace.re = 2*(b*star b).re := by
    have he : (Δ*Δ).trace = 2*(b*star b) := by
      simp only [Δ, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, rank_mul,
        Matrix.trace_smul, rank_trace, hv, hu, huv, hvu, smul_eq_mul]
      linear_combination -2*hab
    rw [he]
    simp
  have hb : 0 ≤ (b*star b).re := by
    have hh : (0:ℂ) ≤ b*star b := by simpa only [mul_comm] using star_mul_self_nonneg b
    exact (Complex.nonneg_iff.mp hh).1
  have hh := OperatorApprox.of_factor (rank v v) (rank u u) Δ P
    (show Δ.IsHermitian from hΔ) hrec htrace
  rw [hcost, hsquare] at hh
  apply hh.weaken
  have hsq := Real.sq_sqrt hb
  have hroot := Real.sq_sqrt (show 0 ≤ 2*(2*(b*star b).re) by positivity)
  nlinarith [Real.sqrt_nonneg (b*star b).re, Real.sqrt_nonneg (2*(2*(b*star b).re))]


def mass (u : e.Basis → ℂ) : ℝ := (bracket u u).re

theorem mass_nonneg (u : e.Basis → ℂ) : 0 ≤ mass u := by
  simpa only [mass, bracket, QKD.CoherentSupport.outer, Matrix.trace, Matrix.diag,
    Matrix.vecMulVec_apply, Pi.star_apply, mul_comm] using
    (Complex.nonneg_iff.mp ((QKD.CoherentSupport.outer_positive u).trace_nonneg)).1

theorem bracket_self (u : e.Basis → ℂ) : bracket u u = (mass u : ℂ) := by
  have h := (Complex.nonneg_iff.mp ((QKD.CoherentSupport.outer_positive u).trace_nonneg)).2
  apply Complex.ext
  · rfl
  · simpa only [QKD.CoherentSupport.outer, Matrix.trace, Matrix.diag,
      Matrix.vecMulVec_apply, Pi.star_apply, mul_comm, bracket, Complex.ofReal_im] using h.symm

theorem mass_eq_zero (u : e.Basis → ℂ) (h : mass u = 0) : u = 0 := by
  apply dotProduct_star_self_eq_zero.mp
  change bracket u u = 0
  rw [bracket_self, h, Complex.ofReal_zero]

def normalize (u : e.Basis → ℂ) : e.Basis → ℂ := (((Real.sqrt (mass u))⁻¹ : ℝ) : ℂ) • u

theorem normalize_unit (u : e.Basis → ℂ) (h : 0 < mass u) :
    bracket (normalize u) (normalize u) = 1 := by
  have hs : Real.sqrt (mass u) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  have hr : (Real.sqrt (mass u))⁻¹ * ((Real.sqrt (mass u))⁻¹ * mass u) = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt (mass_nonneg u)]
  simp only [normalize]
  rw [bracket_smul_left, bracket_smul_right, bracket_self u]
  change star (((Real.sqrt (mass u))⁻¹ : ℝ):ℂ) *
    ((((Real.sqrt (mass u))⁻¹ : ℝ):ℂ) * (mass u:ℂ)) = 1
  rw [show star (((Real.sqrt (mass u))⁻¹ : ℝ):ℂ) =
      (((Real.sqrt (mass u))⁻¹ : ℝ):ℂ) from Complex.conj_ofReal _]
  exact_mod_cast hr

theorem normalize_reconstruct (u : e.Basis → ℂ) (h : 0 < mass u) :
    (Real.sqrt (mass u) : ℂ) • normalize u = u := by
  have hs : Real.sqrt (mass u) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  rw [normalize, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, one_smul]

/-- A normalized projection for arbitrary orthogonal good/bad components.
The bad component may vanish; no division by its norm is required in that case. -/
theorem normalized_projection (x y : e.Basis → ℂ) (hx : 0 < mass x)
    (hxy : bracket x y = 0) (hyx : bracket y x = 0)
    (hn : mass x+mass y = 1) :
    OperatorApprox (rank (x+y) (x+y)) (rank (normalize x) (normalize x)) (Real.sqrt (mass y)) := by
  by_cases hy : mass y = 0
  · have hy0 := mass_eq_zero y hy
    have hx1 : mass x = 1 := by linarith
    have hnrm : normalize x = x := by simp [normalize, hx1]
    rw [hy, Real.sqrt_zero, hy0, add_zero, hnrm]
    exact OperatorApprox.refl _
  · have hyp : 0 < mass y := lt_of_le_of_ne (mass_nonneg y) (Ne.symm hy)
    have hn' : (Real.sqrt (mass x):ℂ)*star (Real.sqrt (mass x):ℂ) +
        (Real.sqrt (mass y):ℂ)*star (Real.sqrt (mass y):ℂ) = 1 := by
      simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (mass_nonneg x), Real.mul_self_sqrt (mass_nonneg y),
        ← Complex.ofReal_add, hn, Complex.ofReal_one]
    have huv : bracket (normalize x) (normalize y) = 0 := by
      simp [normalize, hxy]
    have hvu : bracket (normalize y) (normalize x) = 0 := by
      simp [normalize, hyx]
    have hh := orthogonal_projection (normalize x) (normalize y)
      (Real.sqrt (mass x):ℂ) (Real.sqrt (mass y):ℂ)
      (normalize_unit x hx) (normalize_unit y hyp) huv hvu hn'
    rw [normalize_reconstruct x hx, normalize_reconstruct y hyp] at hh
    simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (mass_nonneg y), Complex.ofReal_re] using hh

end
end Foundation.Quantum.PureProjection
