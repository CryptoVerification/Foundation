import Foundation.Crypto.Semantics.Probability.ClassicalBitRobustBoundary

/-! Signed normalization estimates used by the dyadic boundary construction.
Finite vertex rounding and the geometric mesh locator are separate inputs. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Key : Type*} [Fintype Key]

theorem mass_difference_le (w z : Key → ℝ) : |mass w - mass z| ≤ l1Distance w z := by
  have hpoint (a b : ℝ) : |a| ≤ |a-b| + |b| := by
    have h := abs_add_le (a-b) b
    simpa only [sub_add_cancel] using h
  have hw := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint (w i) (z i)
  have hz := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint (z i) (w i)
  rw [Finset.sum_add_distrib] at hw hz
  simp_rw [abs_sub_comm (z _)] at hz
  change mass w ≤ l1Distance w z + mass z at hw
  change mass z ≤ l1Distance w z + mass w at hz
  apply abs_le.mpr
  constructor <;> linarith

theorem normalized_signed_distance_mul (w z : Key → ℝ) (hw : w ≠ 0) (hz : z ≠ 0) :
    mass z * l1Distance (normalizeSigned w) (normalizeSigned z) ≤ 2 * l1Distance w z := by
  have hp := mass_pos_of_ne_zero w hw
  have hq := mass_pos_of_ne_zero z hz
  have hpoint (i : Key) : mass z * |normalizeSigned w i - normalizeSigned z i| ≤
      |w i - z i| + (|w i| / mass w) * |mass z - mass w| := by
    have heq : mass z * (normalizeSigned w i - normalizeSigned z i) =
        (w i - z i) + (w i / mass w) * (mass z - mass w) := by
      unfold normalizeSigned
      field_simp; ring
    calc
      _ = |mass z * (normalizeSigned w i - normalizeSigned z i)| := by
        rw [abs_mul, abs_of_pos hq]
      _ ≤ |w i-z i| + |(w i / mass w) * (mass z-mass w)| := by
        rw [heq]
        exact abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_div, abs_of_pos hp]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  have hnorm : (∑ i, |w i| / mass w) = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hp)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul] at hs
  have hd := mass_difference_le z w
  have hsym : l1Distance z w = l1Distance w z := by simp only [l1Distance, abs_sub_comm]
  rw [hsym] at hd
  change mass z * l1Distance (normalizeSigned w) (normalizeSigned z) ≤
    l1Distance w z + |mass z - mass w| at hs
  linarith

theorem coordinate_half_distance (w z : Key → ℝ) (hb : bias w = bias z) (i : Key) :
    |w i-z i| ≤ l1Distance w z / 2 := by
  let delta := fun j => w j-z j
  have hd : bias delta = 0 := by
    change (∑ j, (w j-z j)) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hb
  have hsum := mass_parts delta
  have hdiff := bias_parts delta
  have hp : positiveMass delta = mass delta / 2 := by linarith
  have hn : negativeMass delta = mass delta / 2 := by linarith
  by_cases hi : 0 ≤ delta i
  · have hle : max (delta i) 0 ≤ positiveMass delta :=
      Finset.single_le_sum (fun j _ => le_max_right (delta j) 0) (Finset.mem_univ i)
    rw [max_eq_left hi, hp] at hle
    exact (abs_of_nonneg hi) ▸ hle
  · have hi' : delta i ≤ 0 := le_of_not_ge hi
    have hle : max (-delta i) 0 ≤ negativeMass delta :=
      Finset.single_le_sum (fun j _ => le_max_right (-delta j) 0) (Finset.mem_univ i)
    rw [max_eq_left (neg_nonneg.mpr hi'), hn] at hle
    exact (abs_of_nonpos hi') ▸ hle

theorem normalized_coordinate_error_mul (w z : Key → ℝ)
    (hw : w ≠ 0) (hz : z ≠ 0) (hbw : bias w = 0) (hbz : bias z = 0) (i : Key) :
    mass z * |normalizeSigned w i-normalizeSigned z i| ≤ l1Distance w z := by
  have hm := mass_pos_of_ne_zero z hz
  have hcoord := coordinate_half_distance (normalizeSigned w) (normalizeSigned z)
    ((normalizeSigned_bias w hbw).trans (normalizeSigned_bias z hbz).symm) i
  have hnorm := normalized_signed_distance_mul w z hw hz
  nlinarith [mul_le_mul_of_nonneg_left hcoord (le_of_lt hm)]

theorem eight_bit_coordinate_error (w z : Key → ℝ)
    (hbw : bias w = 0) (hbz : bias z = 0)
    (hm : 1 / 3 ≤ mass z) (he : l1Distance w z ≤ 1 / 64) (i : Key) :
    |normalizeSigned w i-normalizeSigned z i| ≤ 3 / 64 := by
  have hz : z ≠ 0 := by
    intro h
    simp [h, mass] at hm
    norm_num at hm
  have hw : w ≠ 0 := by
    intro h
    have he' : mass z ≤ 1 / 64 := by simpa [h, l1Distance, mass] using he
    linarith
  have hcoord := normalized_coordinate_error_mul w z hw hz hbw hbz i
  have hnonneg := abs_nonneg (normalizeSigned w i-normalizeSigned z i)
  nlinarith [mul_le_mul_of_nonneg_right hm hnonneg]

theorem weighted_error_l1_le {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (q d : Point → Key → ℝ) (epsilon : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (he : ∀ i, l1Distance (q i) (d i) ≤ epsilon) :
    l1Distance (∑ i, a i • q i) (∑ i, a i • d i) ≤ epsilon := by
  have hpoint (k : Key) : |(∑ i, a i • q i) k - (∑ i, a i • d i) k| ≤
      ∑ i, a i * |q i k-d i k| := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ i, |a i * (q i k-d i k)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (ha _)]
  have hh := Finset.sum_le_sum (s := Finset.univ) fun k _ => hpoint k
  rw [Finset.sum_comm] at hh
  simp_rw [← Finset.mul_sum] at hh
  have hbound := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (he i) (ha i)
  rw [← Finset.sum_mul, hs, one_mul] at hbound
  exact le_trans hh hbound

theorem weighted_bias_zero {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (q : Point → Key → ℝ) (hz : ∀ i, bias (q i) = 0) :
    bias (∑ i, a i • q i) = 0 := by
  unfold bias
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ i, a i * bias (q i)) = 0
  simp_rw [hz, mul_zero]
  simp

omit [Fintype Key] in
theorem sharpAffine_boundary_mass_lower (x : TetrahedralSimplex)
    (hx : ∃ i, x.val i = 0) : 1 / 3 ≤ mass (sharpAffine x) := by
  obtain ⟨i, hi⟩ := hx
  have hb : bias (sharpAffine x) = bias (0 : Fin 4 → ℝ) := by
    rw [sharpAffine_bias]
    simp [bias]
  have hc := coordinate_half_distance (sharpAffine x) 0 hb i
  have hd : l1Distance (sharpAffine x) 0 = mass (sharpAffine x) := by
    simp [l1Distance, mass]
  rw [hd] at hc
  norm_num [sharpAffine, hi] at hc
  linarith

section Projective
variable {Point : Type*} [Fintype Point]

def boundaryScaleSum (a : Point → ℝ) (p : Point → TetrahedralSimplex) : ℝ :=
  ∑ i, a i * mass (sharpAffine (p i))

def boundaryCoefficient (a : Point → ℝ) (p : Point → TetrahedralSimplex) (i : Point) : ℝ :=
  a i * mass (sharpAffine (p i)) / boundaryScaleSum a p

omit [Fintype Key] in
theorem boundaryScaleSum_bounds (a : Point → ℝ) (p : Point → TetrahedralSimplex)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hp : ∀ i, ∃ k, (p i).val k = 0) :
    1 / 3 ≤ boundaryScaleSum a p ∧ boundaryScaleSum a p ≤ 1 := by
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (sharpAffine_boundary_mass_lower (p i) (hp i)) (ha i)
  have hu := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (sharpAffine_mass_le_one (p i)) (ha i)
  rw [← Finset.sum_mul, hs, one_mul] at hl
  rw [← Finset.sum_mul, hs, one_mul] at hu
  exact ⟨hl, hu⟩

omit [Fintype Key] in
theorem affine_boundary_average (a : Point → ℝ) (p : Point → TetrahedralSimplex)
    (x : TetrahedralSimplex) (hs : ∑ i, a i = 1)
    (hx : ∀ k, ∑ i, a i * (p i).val k = x.val k) (k : Fin 4) :
    (∑ i, a i * sharpAffine (p i) k) = sharpAffine x k := by
  unfold sharpAffine
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  have heq (i : Point) : a i * ((2 / 3 : ℝ) * (p i).val k) =
      (2 / 3 : ℝ) * (a i * (p i).val k) := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum, hx]

omit [Fintype Key] in
/-- Each vertex supplies a local 1/64 l1 rounding certificate. Barycentric
reconstruction and boundary membership then imply the uniform 3/64 coordinate
bound, without a user-supplied global matching map. -/
theorem projective_eight_bit_boundary_error (a : Point → ℝ) (p : Point → TetrahedralSimplex)
    (q : Point → Fin 4 → ℝ) (x : TetrahedralSimplex)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hp : ∀ i, ∃ k, (p i).val k = 0) (hxb : ∃ k, x.val k = 0)
    (hx : ∀ k, ∑ i, a i * (p i).val k = x.val k)
    (hq : ∀ i, bias (q i) = 0)
    (he : ∀ i, l1Distance (q i) (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) (k : Fin 4) :
    |normalizeSigned (∑ i, boundaryCoefficient a p i • q i) k -
      normalizeSigned (sharpAffine x) k| ≤ 3 / 64 := by
  have hd := boundaryScaleSum_bounds a p ha hs hp
  have hdpos : 0 < boundaryScaleSum a p := by linarith [hd.1]
  have hcpos (i : Point) : 0 < mass (sharpAffine (p i)) := by
    have hh := sharpAffine_boundary_mass_lower (p i) (hp i)
    linarith
  have han (i : Point) : 0 ≤ boundaryCoefficient a p i :=
    div_nonneg (mul_nonneg (ha i) (le_of_lt (hcpos i))) (le_of_lt hdpos)
  have has : (∑ i, boundaryCoefficient a p i) = 1 := by
    unfold boundaryCoefficient
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hdpos)
  let z := ∑ i, boundaryCoefficient a p i • normalizeSigned (sharpAffine (p i))
  let w := ∑ i, boundaryCoefficient a p i • q i
  have hcoord (j : Fin 4) : z j = sharpAffine x j / boundaryScaleSum a p := by
    change (∑ i, boundaryCoefficient a p i • normalizeSigned (sharpAffine (p i))) j = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boundaryCoefficient, normalizeSigned]
    have hterm (i : Point) :
        (a i * mass (sharpAffine (p i)) / boundaryScaleSum a p) *
          (sharpAffine (p i) j / mass (sharpAffine (p i))) =
        a i * sharpAffine (p i) j / boundaryScaleSum a p := by
      field_simp [ne_of_gt (hcpos i), ne_of_gt hdpos]
    simp_rw [hterm]
    rw [← Finset.sum_div, affine_boundary_average a p x hs hx]
  have hmass : mass z = mass (sharpAffine x) / boundaryScaleSum a p := by
    unfold mass
    simp_rw [hcoord, abs_div, abs_of_pos hdpos]
    rw [← Finset.sum_div]
  have hmz : 1 / 3 ≤ mass z := by
    rw [hmass]
    apply (le_div_iff₀ hdpos).mpr
    have hh := sharpAffine_boundary_mass_lower x hxb
    linarith [hd.2]
  have hewz : l1Distance w z ≤ 1 / 64 :=
    weighted_error_l1_le (boundaryCoefficient a p) q
      (fun i => normalizeSigned (sharpAffine (p i))) _ han has he
  have hbw : bias w = 0 := weighted_bias_zero _ q hq
  have hbz : bias z = 0 := weighted_bias_zero _ _
    (fun i => normalizeSigned_bias _ (sharpAffine_bias (p i)))
  have hmA : 0 < mass (sharpAffine x) := by
    have hh := sharpAffine_boundary_mass_lower x hxb
    linarith
  have hnz : normalizeSigned z = normalizeSigned (sharpAffine x) := by
    funext j
    unfold normalizeSigned
    rw [hcoord, hmass]
    field_simp
  have herr := eight_bit_coordinate_error w z hbw hbz hmz hewz k
  simpa only [hnz] using herr

end Projective

/-- A finite local rounding witness. Geometry must supply its parameters and
barycentric weights; the arithmetic error estimate is derived below. -/
structure BoundaryRoundingWitness (x : TetrahedralSimplex) (w : Fin 4 → ℝ) where
  count : ℕ
  coefficient : Fin count → ℝ
  parameter : Fin count → TetrahedralSimplex
  rounded : Fin count → Fin 4 → ℝ
  coefficient_nonneg : ∀ i, 0 ≤ coefficient i
  coefficient_sum : ∑ i, coefficient i = 1
  parameter_boundary : ∀ i, ∃ k, (parameter i).val k = 0
  reconstruct : ∀ k, ∑ i, coefficient i * (parameter i).val k = x.val k
  rounded_bias : ∀ i, bias (rounded i) = 0
  rounding_error : ∀ i, l1Distance (rounded i) (normalizeSigned (sharpAffine (parameter i))) ≤ 1 / 64
  mixture : w = ∑ i, boundaryCoefficient coefficient parameter i • rounded i

omit [Fintype Key] in
theorem local_rounding_coordinate_error {x : TetrahedralSimplex} {w : Fin 4 → ℝ}
    (certificate : BoundaryRoundingWitness x w) (hx : ∃ i, x.val i = 0) (k : Fin 4) :
    |normalizeSigned w k-normalizeSigned (sharpAffine x) k| ≤ 3 / 64 := by
  rw [certificate.mixture]
  exact projective_eight_bit_boundary_error certificate.coefficient certificate.parameter
    certificate.rounded x certificate.coefficient_nonneg certificate.coefficient_sum
    certificate.parameter_boundary hx certificate.reconstruct certificate.rounded_bias
    certificate.rounding_error k

omit [Fintype Key] in
theorem locally_rounded_boundary_forces_zero (F : C(TetrahedralSimplex, Fin 4 → ℝ))
    (hb : ∀ x, bias (F x) = 0)
    (hlocal : ∀ x, (∃ i, x.val i = 0) → Nonempty (BoundaryRoundingWitness x (F x))) :
    ∃ x, F x = 0 := by
  apply robust_sharp_extension_forces_zero F hb
  intro x hx k
  obtain ⟨certificate⟩ := hlocal x hx
  exact le_trans (local_rounding_coordinate_error certificate hx k) (by norm_num)

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
