import Foundation.Crypto.Semantics.Probability.ClassicalBitGridGluing

/-! Integer certificates for finite fair-bit signed cipher tables.
The checks are sufficient conditions, not externally trusted assertions. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
variable {Key : Type*} [Fintype Key]

def dyadicVector (D : ℕ) (c : Key → ℤ) (i : Key) : ℝ := (c i : ℝ)/D

def dyadicPerfectCipher (D : ℕ) (hD : 0 < D) (c : Key → ℤ)
    (hb : ∑ i, c i = 0) (hm : ∑ i, |c i| = (D : ℤ)) : PerfectCipher Key where
  signed := dyadicVector D c
  bias_zero := by
    have h : (∑ i, (c i : ℝ)) = 0 := by exact_mod_cast hb
    unfold bias dyadicVector
    rw [← Finset.sum_div, h, zero_div]
  mass_one := by
    have hd : (0 : ℝ) < D := by exact_mod_cast hD
    have h : (∑ i, |(c i : ℝ)|) = (D : ℝ) := by exact_mod_cast hm
    unfold mass dyadicVector
    simp_rw [abs_div, abs_of_pos hd]
    rw [← Finset.sum_div, h, div_self (ne_of_gt hd)]

theorem dyadic_l1_exact (D : ℕ) (hD : 0 < D) (c d : Key → ℤ) :
    l1Distance (dyadicVector D c) (dyadicVector D d) =
      ((∑ i, |c i-d i| : ℤ) : ℝ)/D := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  unfold l1Distance dyadicVector
  simp_rw [← sub_div, abs_div, abs_of_pos hd]
  rw [← Finset.sum_div]
  congr 1
  norm_cast

theorem dyadic_jointTV_exact (D : ℕ) (hD : 0 < D) (c d : Key → ℤ)
    (hbc : ∑ i, c i = 0) (hmc : ∑ i, |c i| = (D : ℤ))
    (hbd : ∑ i, d i = 0) (hmd : ∑ i, |d i| = (D : ℤ)) (message : Bool) :
    jointTV (dyadicPerfectCipher D hD c hbc hmc).toCipher
      (dyadicPerfectCipher D hD d hbd hmd).toCipher message =
      ((∑ i, |c i-d i| : ℤ) : ℝ)/(2*D) := by
  rw [perfect_jointTV]
  change l1Distance (dyadicVector D c) (dyadicVector D d)/2 = _
  rw [dyadic_l1_exact D hD c d]
  ring

theorem eight_bit_jointTV_le (c d : Key → ℤ)
    (hbc : ∑ i, c i = 0) (hmc : ∑ i, |c i| = 256)
    (hbd : ∑ i, d i = 0) (hmd : ∑ i, |d i| = 256)
    (he : ∑ i, |c i-d i| ≤ 148) (message : Bool) :
    jointTV (dyadicPerfectCipher 256 (by omega) c hbc hmc).toCipher
      (dyadicPerfectCipher 256 (by omega) d hbd hmd).toCipher message ≤ 37 / 128 := by
  rw [dyadic_jointTV_exact]
  have h : (∑ i, |(c i : ℝ)-(d i : ℝ)|) ≤ 148 := by exact_mod_cast he
  norm_num
  linarith

omit [Fintype Key] in
/-- Multiplying away the denominators turns each rounding obligation into
an integer inequality. No floating-point error is involved. -/
theorem integer_rounding_coordinate_error (D : ℕ) (hD : 0 < D)
    (c r : Key → ℤ) (L : ℤ) (hL : 0 < L)
    (herror : ∀ i, |c i*L-r i*(D : ℤ)| ≤ L) (i : Key) :
    |(c i : ℝ)/D-(r i : ℝ)/(L : ℝ)| ≤ 1/(D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have he : |(c i : ℝ)*(L : ℝ)-(r i : ℝ)*(D : ℝ)| ≤ (L : ℝ) := by
    exact_mod_cast herror i
  have hformula : (c i : ℝ)/D-(r i : ℝ)/(L : ℝ) =
      ((c i : ℝ)*(L : ℝ)-(r i : ℝ)*(D : ℝ))/((D : ℝ)*(L : ℝ)) := by
    field_simp
  rw [hformula, abs_div, abs_of_pos (mul_pos hd hl)]
  apply (div_le_iff₀ (mul_pos hd hl)).mpr
  have hh : (1/(D : ℝ))*((D : ℝ)*(L : ℝ)) = (L : ℝ) := by
    field_simp
  rw [hh]
  exact he

theorem eight_bit_rounding_l1 (c r : Fin 4 → ℤ)
    (hL : 0 < ∑ i, |r i|)
    (he : ∀ i, |c i*(∑ j, |r j|)-r i*256| ≤ ∑ j, |r j|) :
    l1Distance (dyadicVector 256 c) (normalizeSigned (fun i => (r i : ℝ))) ≤ 1 / 64 := by
  have hm : mass (fun i => (r i : ℝ)) = ((∑ i, |r i| : ℤ) : ℝ) := by
    simp only [mass, Int.cast_sum, Int.cast_abs]
  have hp (i : Fin 4) := integer_rounding_coordinate_error 256 (by omega) c r _ hL he i
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
  change (∑ i, |(c i : ℝ)/256-(r i : ℝ)/((∑ j, |r j| : ℤ) : ℝ)|) ≤ _ at hs
  simp only [normalizeSigned, hm, l1Distance, dyadicVector]
  convert hs using 1 <;> norm_num

theorem normalizeSigned_div_pos (w : Key → ℝ) (C : ℝ) (hC : 0 < C) :
    normalizeSigned (fun i => w i/C) = normalizeSigned w := by
  have hm : mass (fun i => w i/C) = mass w/C := by
    unfold mass
    simp_rw [abs_div, abs_of_pos hC]
    rw [← Finset.sum_div]
  funext i
  unfold normalizeSigned
  rw [hm]
  by_cases hz : mass w = 0
  · simp [hz]
  · field_simp [hz, ne_of_gt hC]

def gridParameterNumerator (n : ℕ) (v : OrderedGridVertex n) (k : Fin 4) : ℤ :=
  if k.val = 0 then (v.val 0).val else
  if k.val = 1 then ((v.val 1).val : ℤ)-(v.val 0).val else
  if k.val = 2 then ((v.val 2).val : ℤ)-(v.val 1).val else (n : ℤ)-(v.val 2).val

def gridSharpNumerator (n : ℕ) (v : OrderedGridVertex n) (k : Fin 4) : ℤ :=
  (n : ℤ)-4*gridParameterNumerator n v k

theorem gridVertexPosition_numerator (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n) (k : Fin 4) :
    (gridVertexPosition n hn v).val k = (gridParameterNumerator n v k : ℝ)/n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  fin_cases k <;> dsimp [gridVertexPosition, simplexOfOrderedCoordinates,
    gridParameterNumerator, gridVertexCoordinate] <;> push_cast <;>
    field_simp [ne_of_gt hN] <;> ring

theorem sharpAffine_grid_numerator (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n) (k : Fin 4) :
    sharpAffine (gridVertexPosition n hn v) k = (gridSharpNumerator n v k : ℝ)/(6*n) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  unfold sharpAffine
  rw [gridVertexPosition_numerator]
  dsimp [gridSharpNumerator]
  push_cast
  field_simp [ne_of_gt hN] <;> ring

theorem normalizeSigned_grid_numerator (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n) :
    normalizeSigned (sharpAffine (gridVertexPosition n hn v)) =
      normalizeSigned (fun k => (gridSharpNumerator n v k : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have he : sharpAffine (gridVertexPosition n hn v) =
      fun k => (gridSharpNumerator n v k : ℝ)/(6*n) :=
    funext (sharpAffine_grid_numerator n hn v)
  rw [he]
  exact normalizeSigned_div_pos _ _ (by positivity)

theorem grid_boundary_integer_error (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n)
    (c : Fin 4 → ℤ) (hL : 0 < ∑ k, |gridSharpNumerator n v k|)
    (he : ∀ k, |c k*(∑ j, |gridSharpNumerator n v j|)-gridSharpNumerator n v k*256| ≤
      ∑ j, |gridSharpNumerator n v j|) :
    l1Distance (dyadicVector 256 c)
      (normalizeSigned (sharpAffine (gridVertexPosition n hn v))) ≤ 1 / 64 := by
  rw [normalizeSigned_grid_numerator]
  exact eight_bit_rounding_l1 c _ hL he

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
