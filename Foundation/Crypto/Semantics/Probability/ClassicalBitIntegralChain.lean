import Foundation.Crypto.Semantics.Probability.ClassicalBitGridComplex

/-! Integer support transfer for the common-face proof. Integer affine
functionals of a grid chain have width at most one; their barycentric
inequalities therefore constrain every vertex with positive weight. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

/-- An integer functional of width at most one cannot average across an
integer upper bound while assigning positive weight above that bound. -/
theorem integral_support_le {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (f : Point → ℤ) (K : ℤ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hw : ∀ i, a i ≠ 0 → ∀ j, a j ≠ 0 → f i ≤ f j+1)
    (hm : ∑ i, a i * (f i : ℝ) ≤ (K : ℝ)) (i : Point) (hi : a i ≠ 0) : f i ≤ K := by
  by_contra h
  have hfi : K+1 ≤ f i := by omega
  have hlow (j : Point) : 0 ≤ a j * ((f j : ℝ)-(K : ℝ)) := by
    by_cases hj : a j = 0
    · simp [hj]
    · have hwidth := hw i hi j hj
      have hfj : K ≤ f j := by omega
      have hfj' : (K : ℝ) ≤ f j := by exact_mod_cast hfj
      exact mul_nonneg (ha j) (sub_nonneg.mpr hfj')
  have hsum : (∑ j, a j * ((f j : ℝ)-(K : ℝ))) ≤ 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    linarith
  have hsingle := Finset.single_le_sum (fun j _ => hlow j) (Finset.mem_univ i)
  have hai : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
  have hfi' : (K : ℝ) < f i := by exact_mod_cast (show K < f i by omega)
  have hpos := mul_pos hai (sub_pos.mpr hfi')
  linarith

theorem integral_support_ge {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (f : Point → ℤ) (K : ℤ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hw : ∀ i, a i ≠ 0 → ∀ j, a j ≠ 0 → f i ≤ f j+1)
    (hm : (K : ℝ) ≤ ∑ i, a i * (f i : ℝ)) (i : Point) (hi : a i ≠ 0) : K ≤ f i := by
  have hw' (u : Point) (hu : a u ≠ 0) (v : Point) (hv : a v ≠ 0) : -f u ≤ -f v+1 := by
    have h := hw v hv u hu
    omega
  have hm' : (∑ j, a j * ((-f j : ℤ) : ℝ)) ≤ ((-K : ℤ) : ℝ) := by
    simpa only [Int.cast_neg, mul_neg, Finset.sum_neg_distrib] using neg_le_neg hm
  have h := integral_support_le a (fun j => -f j) (-K) ha hs hw' hm' i hi
  omega

theorem cubeAxisOrder_bijective (o : Fin 6) : Function.Bijective (cubeAxisOrder o) := by
  fin_cases o <;> decide

theorem cubeVertex_order_coordinate (o : Fin 6) (t : Fin 4) (j : Fin 3) :
    cubeVertex o t (cubeAxisOrder o j) = if j.val < t.val then 1 else 0 := by
  fin_cases o <;> fin_cases t <;> fin_cases j <;>
    dsimp [cubeVertex, cubeAxisOrder]

theorem cubeVertex_sorted (o : Fin 6) (t : Fin 4) : cubeSorted o (cubeVertex o t) := by
  unfold cubeSorted
  rw [cubeVertex_order_coordinate, cubeVertex_order_coordinate, cubeVertex_order_coordinate]
  fin_cases t <;> dsimp <;> norm_num

/-- For any pair of coordinate axes the chain differences lie on one side
of zero. This is stronger than bounding each coordinate independently. -/
theorem cube_difference_one_sided (o : Fin 6) (i j : Fin 3) :
    (∀ t, 0 ≤ cubeVertex o t i-cubeVertex o t j ∧
      cubeVertex o t i-cubeVertex o t j ≤ 1) ∨
    (∀ t, -1 ≤ cubeVertex o t i-cubeVertex o t j ∧
      cubeVertex o t i-cubeVertex o t j ≤ 0) := by
  fin_cases o <;> fin_cases i <;> fin_cases j
  all_goals first
    | (left; intro t; fin_cases t <;> dsimp [cubeVertex, cubeAxisOrder] <;> norm_num; done)
    | (right; intro t; fin_cases t <;> dsimp [cubeVertex, cubeAxisOrder] <;> norm_num)

theorem cube_difference_width (o : Fin 6) (s t : Fin 4) (i j : Fin 3) :
    cubeVertex o s i-cubeVertex o s j ≤ cubeVertex o t i-cubeVertex o t j+1 := by
  rcases cube_difference_one_sided o i j with h | h
  · linarith [(h s).2, (h t).1]
  · linarith [(h s).2, (h t).1]

/-- The only binary points inside a chain's order region are its four vertices. -/
theorem cube_binary_member (o : Fin 6) (z : Fin 3 → ℝ)
    (hb : ∀ j, z j = 0 ∨ z j = 1) (hs : cubeSorted o z) : ∃ t, z = cubeVertex o t := by
  have make (t : Fin 4)
      (h0 : z (cubeAxisOrder o 0) = cubeVertex o t (cubeAxisOrder o 0))
      (h1 : z (cubeAxisOrder o 1) = cubeVertex o t (cubeAxisOrder o 1))
      (h2 : z (cubeAxisOrder o 2) = cubeVertex o t (cubeAxisOrder o 2)) : ∃ t, z = cubeVertex o t := by
    refine ⟨t, ?_⟩
    funext j
    obtain ⟨k, hk⟩ := (cubeAxisOrder_bijective o).2 j
    rw [← hk]
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hn (j : Fin 3) : 0 ≤ z j := by
    rcases hb j with h | h
    · simp [h]
    · simp [h]
  by_cases h0 : z (cubeAxisOrder o 0) = 0
  · have h1 : z (cubeAxisOrder o 1) = 0 := by linarith [hs.2, hn (cubeAxisOrder o 1)]
    have h2 : z (cubeAxisOrder o 2) = 0 := by linarith [hs.1, hn (cubeAxisOrder o 2)]
    apply make 0 <;> simp [cubeVertex_order_coordinate, h0, h1, h2]
  · have h0' : z (cubeAxisOrder o 0) = 1 := (hb _).resolve_left h0
    by_cases h1 : z (cubeAxisOrder o 1) = 0
    · have h2 : z (cubeAxisOrder o 2) = 0 := by linarith [hs.1, hn (cubeAxisOrder o 2)]
      apply make 1 <;> simp [cubeVertex_order_coordinate, h0', h1, h2]
    · have h1' : z (cubeAxisOrder o 1) = 1 := (hb _).resolve_left h1
      rcases hb (cubeAxisOrder o 2) with h2 | h2
      · apply make 2 <;> simp [cubeVertex_order_coordinate, h0', h1', h2]
      · apply make 3 <;> simp [cubeVertex_order_coordinate, h0', h1', h2]

/-- Integer points satisfying a translated chain's box and order inequalities
are actual chain vertices. -/
theorem integral_chain_region_member (o : Fin 6) (b m : Fin 3 → ℤ)
    (hb : ∀ j, b j ≤ m j ∧ m j ≤ b j+1)
    (hs : cubeSorted o (fun j => (m j : ℝ)-(b j : ℝ))) :
    ∃ t, ∀ j, (m j : ℝ) = (b j : ℝ)+cubeVertex o t j := by
  have hbinary (j : Fin 3) : ((m j : ℝ)-(b j : ℝ)) = 0 ∨ ((m j : ℝ)-(b j : ℝ)) = 1 := by
    have h := hb j
    have he : m j = b j ∨ m j = b j+1 := by omega
    rcases he with h | h
    · left; rw [h]; ring
    · right; rw [h]; push_cast; ring
  obtain ⟨t, ht⟩ := cube_binary_member o _ hbinary hs
  refine ⟨t, ?_⟩
  intro j
  have h := congrFun ht j
  linarith

/-- Average an integer inequality holding on all vertices with nonzero weight. -/
theorem integral_average_le {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (f : Point → ℤ) (K : ℤ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hf : ∀ i, a i ≠ 0 → f i ≤ K) : ∑ i, a i * (f i : ℝ) ≤ (K : ℝ) := by
  calc
    _ ≤ ∑ i, a i * (K : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : a i = 0
      · simp [hi]
      · have h : (f i : ℝ) ≤ K := by exact_mod_cast hf i hi
        exact mul_le_mul_of_nonneg_left h (ha i)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

theorem integral_average_ge {Point : Type*} [Fintype Point]
    (a : Point → ℝ) (f : Point → ℤ) (K : ℤ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hf : ∀ i, a i ≠ 0 → K ≤ f i) : (K : ℝ) ≤ ∑ i, a i * (f i : ℝ) := by
  calc
    _ = ∑ i, a i * (K : ℝ) := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : a i = 0
      · simp [hi]
      · have h : (K : ℝ) ≤ f i := by exact_mod_cast hf i hi
        exact mul_le_mul_of_nonneg_left h (ha i)

def gridIntegralCoordinate {n : ℕ} (v : OrderedGridVertex n) (j : Fin 3) : ℤ := (v.val j).val

theorem gridIntegralCoordinate_injective (n : ℕ) :
    Function.Injective (fun v : OrderedGridVertex n => gridIntegralCoordinate v) := by
  intro v w he
  apply Subtype.ext
  funext j
  apply Fin.ext
  have h := congrFun he j
  change (((v.val j).val : ℤ)) = ((w.val j).val : ℤ) at h
  exact_mod_cast h

theorem gridChain_integral_coordinate (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v)
    (t : Fin 4) (j : Fin 3) :
    (gridIntegralCoordinate (v t) j : ℝ) = ((base j).val : ℝ)+cubeVertex o t j := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hv t j
  change ((v t).val j).val / (n : ℝ) = (((base j).val : ℝ)+cubeVertex o t j)/n at h
  have hh := (div_left_inj' (ne_of_gt hN)).mp h
  simpa only [gridIntegralCoordinate, Int.cast_natCast] using hh

theorem gridChain_coordinate_width (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v)
    (s t : Fin 4) (j : Fin 3) :
    gridIntegralCoordinate (v s) j ≤ gridIntegralCoordinate (v t) j+1 := by
  have hreal : (gridIntegralCoordinate (v s) j : ℝ) ≤ (gridIntegralCoordinate (v t) j : ℝ)+1 := by
    rw [gridChain_integral_coordinate n hn base o v hv, gridChain_integral_coordinate n hn base o v hv]
    linarith [(cubeVertex_bounds o s j).2, (cubeVertex_bounds o t j).1]
  exact_mod_cast hreal

theorem gridChain_difference_width (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v)
    (s t : Fin 4) (i j : Fin 3) :
    gridIntegralCoordinate (v s) i-gridIntegralCoordinate (v s) j ≤
      gridIntegralCoordinate (v t) i-gridIntegralCoordinate (v t) j+1 := by
  have hreal : ((gridIntegralCoordinate (v s) i-gridIntegralCoordinate (v s) j : ℤ) : ℝ) ≤
      ((gridIntegralCoordinate (v t) i-gridIntegralCoordinate (v t) j : ℤ) : ℝ)+1 := by
    push_cast
    rw [gridChain_integral_coordinate n hn base o v hv,
      gridChain_integral_coordinate n hn base o v hv,
      gridChain_integral_coordinate n hn base o v hv,
      gridChain_integral_coordinate n hn base o v hv]
    linarith [cube_difference_width o s t i j]
  exact_mod_cast hreal

/-- Satisfying a valid chain's integer region puts a table vertex in that
chain's actual finite vertex set, rather than merely its bounding box. -/
theorem gridChain_region_member (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v)
    (w : OrderedGridVertex n)
    (hb : ∀ j, ((base j).val : ℤ) ≤ gridIntegralCoordinate w j ∧
      gridIntegralCoordinate w j ≤ ((base j).val : ℤ)+1)
    (hs : cubeSorted o (fun j => (gridIntegralCoordinate w j : ℝ)-((base j).val : ℝ))) :
    w ∈ Finset.univ.image v := by
  let b : Fin 3 → ℤ := fun j => (base j).val
  have hs' : cubeSorted o (fun j => (gridIntegralCoordinate w j : ℝ)-(b j : ℝ)) := by
    simpa only [b, Int.cast_natCast] using hs
  obtain ⟨t, ht⟩ := integral_chain_region_member o b (gridIntegralCoordinate w) hb hs'
  have heq : gridIntegralCoordinate w = gridIntegralCoordinate (v t) := by
    funext j
    apply Int.cast_injective (α := ℝ)
    rw [ht j, gridChain_integral_coordinate n hn base o v hv t j]
    simp only [b, Int.cast_natCast]
  have hw := gridIntegralCoordinate_injective n heq
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hw.symm⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
