import Foundation.Crypto.Semantics.Probability.ClassicalBitMeshGeometry

/-! The six chain tetrahedra cover every point of a three-dimensional cube.
All statements quantify over real points, not a finite set of sample points.
Restriction to ordered cumulative coordinates and global gluing are separate. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

def cubeAxisOrder (o : Fin 6) (j : Fin 3) : Fin 3 :=
  match o.val with
  | 0 => j
  | 1 => if j.val = 0 then 0 else if j.val = 1 then 2 else 1
  | 2 => if j.val = 0 then 1 else if j.val = 1 then 0 else 2
  | 3 => if j.val = 0 then 1 else if j.val = 1 then 2 else 0
  | 4 => if j.val = 0 then 2 else if j.val = 1 then 0 else 1
  | _ => if j.val = 0 then 2 else if j.val = 1 then 1 else 0

def cubeVertex (o : Fin 6) (t : Fin 4) (j : Fin 3) : ℝ :=
  if t.val = 0 then 0 else if t.val = 3 then 1 else
    if t.val = 1 then (if j.val = (cubeAxisOrder o 0).val then 1 else 0)
    else (if j.val = (cubeAxisOrder o 0).val ∨ j.val = (cubeAxisOrder o 1).val then 1 else 0)

def cubeWeights (o : Fin 6) (z : Fin 3 → ℝ) (t : Fin 4) : ℝ :=
  if t.val = 0 then 1-z (cubeAxisOrder o 0) else
  if t.val = 1 then z (cubeAxisOrder o 0)-z (cubeAxisOrder o 1) else
  if t.val = 2 then z (cubeAxisOrder o 1)-z (cubeAxisOrder o 2) else z (cubeAxisOrder o 2)

def cubeSorted (o : Fin 6) (z : Fin 3 → ℝ) : Prop :=
  z (cubeAxisOrder o 2) ≤ z (cubeAxisOrder o 1) ∧
    z (cubeAxisOrder o 1) ≤ z (cubeAxisOrder o 0)

theorem cube_order_exists (z : Fin 3 → ℝ) : ∃ o, cubeSorted o z := by
  by_cases h01 : z 1 ≤ z 0
  · by_cases h12 : z 2 ≤ z 1
    · exact ⟨0, h12, h01⟩
    · by_cases h02 : z 2 ≤ z 0
      · exact ⟨1, le_of_not_ge h12, h02⟩
      · exact ⟨4, h01, le_of_not_ge h02⟩
  · by_cases h02 : z 2 ≤ z 0
    · exact ⟨2, h02, le_of_not_ge h01⟩
    · by_cases h12 : z 2 ≤ z 1
      · exact ⟨3, le_of_not_ge h02, h12⟩
      · exact ⟨5, le_of_not_ge h01, le_of_not_ge h12⟩

theorem cubeWeights_sum (o : Fin 6) (z : Fin 3 → ℝ) : ∑ t, cubeWeights o z t = 1 := by
  simp [cubeWeights, Fin.sum_univ_four]

theorem cubeWeights_nonneg (o : Fin 6) (z : Fin 3 → ℝ)
    (hb : ∀ j, 0 ≤ z j ∧ z j ≤ 1) (hs : cubeSorted o z) :
    ∀ t, 0 ≤ cubeWeights o z t := by
  intro t
  have h0 := hb (cubeAxisOrder o 0)
  have h2 := hb (cubeAxisOrder o 2)
  rcases hs with ⟨h21, h10⟩
  fin_cases t <;> simp [cubeWeights] <;> linarith

theorem cube_chain_coordinate (o : Fin 6) (a : Fin 4 → ℝ) (j : Fin 3) :
    (∑ t, a t * cubeVertex o t (cubeAxisOrder o j)) =
      (if j.val = 0 then a 1+a 2+a 3 else if j.val = 1 then a 2+a 3 else a 3) := by
  fin_cases o <;> fin_cases j <;>
    simp only [Fin.sum_univ_four] <;> dsimp [cubeVertex, cubeAxisOrder] <;> ring

theorem cubeWeights_reconstruct (o : Fin 6) (z : Fin 3 → ℝ) (j : Fin 3) :
    (∑ t, cubeWeights o z t * cubeVertex o t j) = z j := by
  fin_cases o <;> fin_cases j <;>
    simp only [Fin.sum_univ_four] <;> dsimp [cubeWeights, cubeVertex, cubeAxisOrder] <;> ring

/-- Every point of the cube has a four-vertex certificate in one of six cells. -/
theorem cube_chain_cover (z : Fin 3 → ℝ) (hb : ∀ j, 0 ≤ z j ∧ z j ≤ 1) :
    ∃ o : Fin 6, (∀ t, 0 ≤ cubeWeights o z t) ∧
      (∑ t, cubeWeights o z t = 1) ∧
      (∀ j, ∑ t, cubeWeights o z t * cubeVertex o t j = z j) := by
  obtain ⟨o, ho⟩ := cube_order_exists z
  exact ⟨o, cubeWeights_nonneg o z hb ho, cubeWeights_sum o z, cubeWeights_reconstruct o z⟩

/-- The coordinate differences recover all four affine coefficients. -/
theorem cubeWeights_recover (o : Fin 6) (a : Fin 4 → ℝ) (z : Fin 3 → ℝ)
    (ha : ∑ t, a t = 1)
    (hz : ∀ j, ∑ t, a t * cubeVertex o t j = z j) : a = cubeWeights o z := by
  have h0 := cube_chain_coordinate o a 0
  have h1 := cube_chain_coordinate o a 1
  have h2 := cube_chain_coordinate o a 2
  rw [hz] at h0 h1 h2
  dsimp at h0 h1 h2
  have hsum : a 0+a 1+a 2+a 3 = 1 := by simpa [Fin.sum_univ_four, add_assoc] using ha
  funext t
  fin_cases t <;> simp [cubeWeights] <;> linarith

theorem cube_chain_affineIndependent (o : Fin 6) :
    AffineIndependent ℝ (cubeVertex o) := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb he
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha,
    Finset.affineCombination_eq_linear_combination _ _ _ hb] at he
  let z := ∑ t, a t • cubeVertex o t
  have hza (j : Fin 3) : ∑ t, a t * cubeVertex o t j = z j := by
    simp [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hzb (j : Fin 3) : ∑ t, b t * cubeVertex o t j = z j := by
    have h := congrFun he j
    simpa [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  exact (cubeWeights_recover o a z ha hza).trans (cubeWeights_recover o b z hb hzb).symm

def gridCubeVertex (n : ℝ) (base : Fin 3 → ℝ) (o : Fin 6) (t : Fin 4) (j : Fin 3) : ℝ :=
  (base j+cubeVertex o t j)/n

/-- Translation and a positive mesh scale preserve the all-point cover. -/
theorem grid_cube_chain_cover (n : ℝ) (hn : 0 < n) (base y : Fin 3 → ℝ)
    (hb : ∀ j, 0 ≤ n*y j-base j ∧ n*y j-base j ≤ 1) :
    ∃ o : Fin 6, ∃ a : Fin 4 → ℝ, (∀ t, 0 ≤ a t) ∧ (∑ t, a t = 1) ∧
      ∀ j, ∑ t, a t * gridCubeVertex n base o t j = y j := by
  obtain ⟨o, ha, hs, hz⟩ := cube_chain_cover (fun j => n*y j-base j) hb
  refine ⟨o, cubeWeights o (fun j => n*y j-base j), ha, hs, ?_⟩
  intro j
  simp only [gridCubeVertex, ← mul_div_assoc, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, hz]
  field_simp [ne_of_gt hn]
  ring

/-- Equal fractional coordinates are ordered by decreasing axis number. -/
def cubeStableSorted (o : Fin 6) (z : Fin 3 → ℝ) : Prop :=
  match o.val with
  | 0 => z 2 < z 1 ∧ z 1 < z 0
  | 1 => z 1 ≤ z 2 ∧ z 2 < z 0
  | 2 => z 2 < z 0 ∧ z 0 ≤ z 1
  | 3 => z 0 ≤ z 2 ∧ z 2 < z 1
  | 4 => z 1 < z 0 ∧ z 0 ≤ z 2
  | _ => z 0 ≤ z 1 ∧ z 1 ≤ z 2

theorem cube_stable_order_exists (z : Fin 3 → ℝ) : ∃ o, cubeStableSorted o z := by
  by_cases h01 : z 1 < z 0
  · by_cases h12 : z 2 < z 1
    · exact ⟨0, h12, h01⟩
    · by_cases h02 : z 2 < z 0
      · exact ⟨1, le_of_not_gt h12, h02⟩
      · exact ⟨4, h01, le_of_not_gt h02⟩
  · by_cases h02 : z 2 < z 0
    · exact ⟨2, h02, le_of_not_gt h01⟩
    · by_cases h12 : z 2 < z 1
      · exact ⟨3, le_of_not_gt h02, h12⟩
      · exact ⟨5, le_of_not_gt h01, le_of_not_gt h12⟩

theorem cube_stable_sorted (o : Fin 6) (z : Fin 3 → ℝ)
    (hs : cubeStableSorted o z) : cubeSorted o z := by
  fin_cases o <;> norm_num [cubeStableSorted, cubeSorted, cubeAxisOrder] at hs ⊢
  all_goals constructor <;> linarith [hs.1, hs.2]

/-- Integral adjacent base coordinates are equal or separated by at least one.
The stable tie rule keeps every chain vertex in the ordered chamber. -/
theorem cube_stable_chain_ordered (o : Fin 6) (base z : Fin 3 → ℝ)
    (hs : cubeStableSorted o z)
    (hb01 : base 0 = base 1 ∨ base 0+1 ≤ base 1)
    (hb12 : base 1 = base 2 ∨ base 1+1 ≤ base 2)
    (hy01 : base 0+z 0 ≤ base 1+z 1) (hy12 : base 1+z 1 ≤ base 2+z 2) :
    ∀ t, base 0+cubeVertex o t 0 ≤ base 1+cubeVertex o t 1 ∧
      base 1+cubeVertex o t 1 ≤ base 2+cubeVertex o t 2 := by
  intro t
  fin_cases o <;> fin_cases t <;>
    dsimp [cubeStableSorted, cubeVertex, cubeAxisOrder] at hs ⊢
  all_goals rcases hb01 with h01 | h01
  all_goals rcases hb12 with h12 | h12
  all_goals constructor <;> linarith [hs.1, hs.2]

theorem cubeVertex_bounds (o : Fin 6) (t : Fin 4) (j : Fin 3) :
    0 ≤ cubeVertex o t j ∧ cubeVertex o t j ≤ 1 := by
  fin_cases o <;> fin_cases t <;> fin_cases j <;>
    dsimp [cubeVertex, cubeAxisOrder] <;> norm_num

/-- A single ordered grid cube has a valid chain certificate, including ties. -/
theorem ordered_grid_cube_cover (n : ℝ) (hn : 0 < n) (base y : Fin 3 → ℝ)
    (hb01 : base 0 = base 1 ∨ base 0+1 ≤ base 1)
    (hb12 : base 1 = base 2 ∨ base 1+1 ≤ base 2)
    (hy01 : y 0 ≤ y 1) (hy12 : y 1 ≤ y 2)
    (hb : ∀ j, 0 ≤ n*y j-base j ∧ n*y j-base j ≤ 1) :
    ∃ o : Fin 6, ∃ a : Fin 4 → ℝ, (∀ t, 0 ≤ a t) ∧ (∑ t, a t = 1) ∧
      (∀ j, ∑ t, a t * gridCubeVertex n base o t j = y j) ∧
      (∀ t, gridCubeVertex n base o t 0 ≤ gridCubeVertex n base o t 1 ∧
        gridCubeVertex n base o t 1 ≤ gridCubeVertex n base o t 2) := by
  let z := fun j => n*y j-base j
  obtain ⟨o, ho⟩ := cube_stable_order_exists z
  let a := cubeWeights o z
  have ha := cubeWeights_nonneg o z hb (cube_stable_sorted o z ho)
  have hs := cubeWeights_sum o z
  refine ⟨o, a, ha, hs, ?_, ?_⟩
  · intro j
    change (∑ t, cubeWeights o z t * gridCubeVertex n base o t j) = y j
    simp only [gridCubeVertex, ← mul_div_assoc, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul,
      cubeWeights_reconstruct]
    dsimp [z]
    field_simp [ne_of_gt hn]
    ring
  · intro t
    have h01 : base 0+z 0 ≤ base 1+z 1 := by
      dsimp [z]; nlinarith [mul_le_mul_of_nonneg_left hy01 (le_of_lt hn)]
    have h12 : base 1+z 1 ≤ base 2+z 2 := by
      dsimp [z]; nlinarith [mul_le_mul_of_nonneg_left hy12 (le_of_lt hn)]
    have hc := cube_stable_chain_ordered o base z ho hb01 hb12 h01 h12 t
    exact ⟨div_le_div_of_nonneg_right hc.1 (le_of_lt hn),
      div_le_div_of_nonneg_right hc.2 (le_of_lt hn)⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
