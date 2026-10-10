import Foundation.Quantum.QKD.SubnormalizedGuess

/-! Finite operator version of the small-superposition estimate. The coherent
sum of R vectors is bounded by R times their incoherent covariance. No guessing
or secrecy inequality is assumed. The algebraic positive witness is a sum of
outer products of pairwise differences. -/
namespace Foundation.Quantum.QKD.CoherentSupport
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {I : Type} {e a : Space}

def outer (v : e.Basis → ℂ) : Operator e := Matrix.vecMulVec v (star v)

theorem outer_positive (v : e.Basis → ℂ) : (outer v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem outer_scale (c : ℂ) (v : e.Basis → ℂ) : outer (c • v) = (c*star c) • outer v := by
  ext i j
  simp only [outer, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul, Matrix.smul_apply]
  ring

/-- The exact positive witness for loss by the support cardinality. -/
theorem variance_identity (J : Finset I) (v : I → e.Basis → ℂ) :
    (J.card:ℂ) • (∑ i ∈ J, outer (v i)) - outer (∑ i ∈ J, v i) =
      (1/2:ℂ) • ∑ i ∈ J, ∑ j ∈ J, outer (v i-v j) := by
  ext u w
  simp only [outer, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Pi.sub_apply, Pi.star_apply, Finset.sum_apply, star_sum, star_sub, smul_eq_mul]
  have hdiag : (∑ i ∈ J, ∑ j ∈ J, v i u * star (v i w)) =
      (J.card:ℂ) * ∑ i ∈ J, v i u * star (v i w) := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hdiag' : (∑ i ∈ J, ∑ j ∈ J, v j u * star (v j w)) =
      (J.card:ℂ) * ∑ i ∈ J, v i u * star (v i w) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hcross : (∑ i ∈ J, ∑ j ∈ J, v i u * star (v j w)) =
      (∑ i ∈ J, v i u) * (∑ i ∈ J, star (v i w)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hcross' : (∑ i ∈ J, ∑ j ∈ J, v j u * star (v i w)) =
      (∑ i ∈ J, v i u) * (∑ i ∈ J, star (v i w)) := by
    rw [Finset.sum_comm]
    exact hcross
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hcross, hcross', hdiag']
  ring

/-- Coherence among R amplitudes costs at most R in positive-operator order. -/
theorem sum_dominated (J : Finset I) (v : I → e.Basis → ℂ) :
    ((J.card:ℂ) • (∑ i ∈ J, outer (v i)) - outer (∑ i ∈ J, v i)).PosSemidef := by
  rw [variance_identity]
  exact (Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_sum _
    (fun j _ => outer_positive (v i-v j)))).smul (Complex.nonneg_iff.mpr (by norm_num))

/-- Equal-modulus basis coefficients give an explicit reference covariance bound. -/
theorem flat_dominated (J : Finset I) (v : I → e.Basis → ℂ) (c : I → ℂ) (r : ℝ)
    (hc : ∀ i ∈ J, c i * star (c i) = (r:ℂ)) :
    ((((J.card:ℝ)*r:ℝ):ℂ) • (∑ i ∈ J, outer (v i)) -
      outer (∑ i ∈ J, c i • v i)).PosSemidef := by
  have h := sum_dominated J (fun i => c i • v i)
  have hs : (∑ i ∈ J, outer (c i • v i)) = (r:ℂ) • ∑ i ∈ J, outer (v i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [outer_scale, hc i hi]
  rw [hs, smul_smul] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using h

/-- The actual synthesis matrix has zero columns outside the chosen support. -/
def synthesis (J : Finset a.Basis) (v : a.Basis → e.Basis → ℂ) : Op a e :=
  fun u i => if i ∈ J then v i u else 0

def amplitude (J : Finset a.Basis) (U : Operator a) (v : a.Basis → e.Basis → ℂ) (z : a.Basis) : e.Basis → ℂ :=
  ∑ i ∈ J, U i z • v i

theorem column_covariance (M : Op a e) : M*M.conjTranspose = ∑ i, outer (fun u => M u i) := by
  ext u w
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, outer, Matrix.vecMulVec_apply, Matrix.sum_apply]

theorem synthesis_covariance (J : Finset a.Basis) (v : a.Basis → e.Basis → ℂ) :
    synthesis J v * (synthesis J v).conjTranspose = ∑ i ∈ J, outer (v i) := by
  rw [column_covariance]
  ext u w
  simp only [synthesis, outer, Matrix.vecMulVec_apply, Matrix.sum_apply,
    Pi.star_apply, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi]

theorem amplitude_matrix (J : Finset a.Basis) (U : Operator a) (v : a.Basis → e.Basis → ℂ)
    (u : e.Basis) (z : a.Basis) : (synthesis J v * U) u z = amplitude J U v z u := by
  simp [synthesis, amplitude, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_ite_mem, mul_comm]

/-- A verified coisometry preserves the whole auxiliary covariance under
measurement. It does not merely preserve the scalar trace. -/
theorem measurement_covariance (J : Finset a.Basis) (U : Operator a) (v : a.Basis → e.Basis → ℂ)
    (hU : U*U.conjTranspose = 1) :
    (∑ z, outer (amplitude J U v z)) = ∑ i ∈ J, outer (v i) := by
  have hm := column_covariance (synthesis J v * U)
  have ha (z : a.Basis) : (fun u => (synthesis J v * U) u z) = amplitude J U v z := by
    funext u
    exact amplitude_matrix J U v u z
  simp_rw [ha] at hm
  rw [← hm, Matrix.conjTranspose_mul]
  calc
    _ = synthesis J v * (U*U.conjTranspose) * (synthesis J v).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, synthesis_covariance]

/-- Normalization is an input-vector normalization, not a secrecy premise. -/
def reference (J : Finset a.Basis) (v : a.Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, outer (v i)).trace = 1) : Density e where
  matrix := ∑ i ∈ J, outer (v i)
  positive := Matrix.posSemidef_sum _ (fun i _ => outer_positive (v i))
  normalized := hn

def measured (J : Finset a.Basis) (U : Operator a) (v : a.Basis → e.Basis → ℂ)
    (hU : U*U.conjTranspose = 1) (hn : (∑ i ∈ J, outer (v i)).trace = 1) : Guessing.CQ a.Basis e where
  block z := outer (amplitude J U v z)
  positive z := outer_positive _
  normalized := by
    rw [← Matrix.trace_sum, measurement_covariance J U v hU, hn]

/-- The positive-operator certificate required by privacy amplification is
constructed from the complementary support and the actual measurement matrix. -/
theorem measured_dominated (J : Finset a.Basis) (U : Operator a) (v : a.Basis → e.Basis → ℂ)
    (hU : U*U.conjTranspose = 1) (hn : (∑ i ∈ J, outer (v i)).trace = 1)
    (r : ℝ) (hc : ∀ i ∈ J, ∀ z, U i z * star (U i z) = (r:ℂ)) :
    Subnormalized.Dominated (Subnormalized.ofCQ (measured J U v hU hn)) (reference J v hn) ((J.card:ℝ)*r) := by
  intro z
  exact flat_dominated J v (fun i => U i z) r (fun i hi => hc i hi z)

end
end Foundation.Quantum.QKD.CoherentSupport
