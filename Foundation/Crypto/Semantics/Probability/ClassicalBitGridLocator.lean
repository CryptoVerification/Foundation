import Foundation.Crypto.Semantics.Probability.ClassicalBitCubeTriangulation
import Mathlib.Algebra.Order.Floor.Semiring

/-! A capped natural floor selects a valid grid cube, including the upper
boundary. Its stable chain covers every ordered real parameter point. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

def gridBase (n : ℕ) (y : ℝ) : ℕ := min ⌊(n : ℝ)*y⌋₊ (n-1)

theorem gridBase_lt (n : ℕ) (hn : 0 < n) (y : ℝ) : gridBase n y < n := by
  have h := min_le_right ⌊(n : ℝ)*y⌋₊ (n-1)
  dsimp [gridBase]
  omega

theorem gridBase_mono (n : ℕ) {y z : ℝ} (hyz : y ≤ z) : gridBase n y ≤ gridBase n z :=
  min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left hyz (Nat.cast_nonneg n)))

theorem gridBase_residual (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ (n : ℝ)*y-gridBase n y ∧ (n : ℝ)*y-gridBase n y ≤ 1 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor := Nat.floor_le (mul_nonneg (le_of_lt hN) hy.1)
  have hbase : (gridBase n y : ℝ) ≤ ⌊(n : ℝ)*y⌋₊ := by
    exact_mod_cast min_le_left ⌊(n : ℝ)*y⌋₊ (n-1)
  refine ⟨by linarith, ?_⟩
  by_cases h : ⌊(n : ℝ)*y⌋₊ ≤ n-1
  · have hlt := Nat.lt_floor_add_one ((n : ℝ)*y)
    rw [gridBase, min_eq_left h]
    linarith
  · have heq : gridBase n y = n-1 := min_eq_right (le_of_not_ge h)
    rw [heq, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hy.2 (le_of_lt hN)]

theorem natural_base_gap {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) = b ∨ (a : ℝ)+1 ≤ b := by
  by_cases h : a = b
  · exact Or.inl (congrArg Nat.cast h)
  · right
    have hh : a+1 ≤ b := by omega
    exact_mod_cast hh

/-- The grid locator covers every real point in the ordered unit chamber.
No finite sampling or supplied cube selection occurs in this statement. -/
theorem ordered_unit_grid_cover (n : ℕ) (hn : 0 < n) (y : Fin 3 → ℝ)
    (hy0 : 0 ≤ y 0) (hy01 : y 0 ≤ y 1) (hy12 : y 1 ≤ y 2) (hy2 : y 2 ≤ 1) :
    ∃ o : Fin 6, ∃ a : Fin 4 → ℝ, (∀ t, 0 ≤ a t) ∧ (∑ t, a t = 1) ∧
      (∀ j, ∑ t, a t * gridCubeVertex n (fun j => gridBase n (y j)) o t j = y j) ∧
      (∀ t, gridCubeVertex n (fun j => gridBase n (y j)) o t 0 ≤
          gridCubeVertex n (fun j => gridBase n (y j)) o t 1 ∧
        gridCubeVertex n (fun j => gridBase n (y j)) o t 1 ≤
          gridCubeVertex n (fun j => gridBase n (y j)) o t 2) ∧
      (∀ t j, 0 ≤ gridCubeVertex n (fun j => gridBase n (y j)) o t j ∧
        gridCubeVertex n (fun j => gridBase n (y j)) o t j ≤ 1) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hy (j : Fin 3) : 0 ≤ y j ∧ y j ≤ 1 := by
    fin_cases j <;> dsimp <;> constructor <;> linarith
  let base : Fin 3 → ℝ := fun j => gridBase n (y j)
  obtain ⟨o, a, ha, hs, hr, ho⟩ := ordered_grid_cube_cover n hN base y
    (natural_base_gap (gridBase_mono n hy01)) (natural_base_gap (gridBase_mono n hy12))
    hy01 hy12 (fun j => gridBase_residual n hn (y j) (hy j))
  refine ⟨o, a, ha, hs, hr, ho, ?_⟩
  intro t j
  have hc := cubeVertex_bounds o t j
  have hb0 : (0 : ℝ) ≤ base j := Nat.cast_nonneg _
  have hb1 : base j+1 ≤ (n : ℝ) := by
    have hh := gridBase_lt n hn (y j)
    have hh' : gridBase n (y j)+1 ≤ n := by omega
    change (gridBase n (y j) : ℝ)+1 ≤ (n : ℝ)
    exact_mod_cast hh'
  constructor
  · exact div_nonneg (add_nonneg hb0 hc.1) (le_of_lt hN)
  · apply (div_le_one hN).mpr
    linarith [hc.2]

theorem cubeVertex_integral (o : Fin 6) (t : Fin 4) (j : Fin 3) :
    ∃ m : ℕ, m ≤ 1 ∧ cubeVertex o t j = (m : ℝ) := by
  unfold cubeVertex
  split_ifs <;> first
    | (refine ⟨0, by omega, ?_⟩; norm_num; done)
    | (refine ⟨1, le_rfl, ?_⟩; norm_num)

/-- Every selected chain vertex belongs to the finite rational grid. -/
theorem located_vertex_integral (n : ℕ) (hn : 0 < n) (y : Fin 3 → ℝ)
    (o : Fin 6) (t : Fin 4) :
    ∃ v : Fin 3 → ℕ, (∀ j, v j ≤ n) ∧ ∀ j,
      gridCubeVertex n (fun j => gridBase n (y j)) o t j = (v j : ℝ)/n := by
  choose m hm he using cubeVertex_integral o t
  refine ⟨fun j => gridBase n (y j)+m j, ?_, ?_⟩
  · intro j
    have h := gridBase_lt n hn (y j)
    have h' := hm j
    change gridBase n (y j)+m j ≤ n
    omega
  · intro j
    simp only [gridCubeVertex, he j, Nat.cast_add]

def cumulativeCoordinate (x : TetrahedralSimplex) (j : Fin 3) : ℝ :=
  if j.val = 0 then x.val 0 else if j.val = 1 then x.val 0+x.val 1
  else x.val 0+x.val 1+x.val 2

theorem cumulativeCoordinate_ordered (x : TetrahedralSimplex) :
    0 ≤ cumulativeCoordinate x 0 ∧ cumulativeCoordinate x 0 ≤ cumulativeCoordinate x 1 ∧
      cumulativeCoordinate x 1 ≤ cumulativeCoordinate x 2 ∧ cumulativeCoordinate x 2 ≤ 1 := by
  have h0 := x.property.1 0
  have h1 := x.property.1 1
  have h2 := x.property.1 2
  have h3 := x.property.1 3
  have hs : x.val 0+x.val 1+x.val 2+x.val 3 = 1 := by
    simpa [Fin.sum_univ_four, add_assoc] using x.property.2
  dsimp [cumulativeCoordinate]
  exact ⟨h0, by linarith, by linarith, by linarith⟩

def simplexOfOrderedCoordinates (r : Fin 3 → ℝ) (h0 : 0 ≤ r 0)
    (h01 : r 0 ≤ r 1) (h12 : r 1 ≤ r 2) (h2 : r 2 ≤ 1) : TetrahedralSimplex :=
  ⟨fun k => if k.val = 0 then r 0 else if k.val = 1 then r 1-r 0
    else if k.val = 2 then r 2-r 1 else 1-r 2, by
    constructor
    · intro k
      fin_cases k <;> dsimp <;> linarith
    · simp only [Fin.sum_univ_four]
      dsimp
      ring⟩

theorem orderedCoordinates_cumulative (r : Fin 3 → ℝ) (h0 : 0 ≤ r 0)
    (h01 : r 0 ≤ r 1) (h12 : r 1 ≤ r 2) (h2 : r 2 ≤ 1) (j : Fin 3) :
    cumulativeCoordinate (simplexOfOrderedCoordinates r h0 h01 h12 h2) j = r j := by
  fin_cases j <;> dsimp [cumulativeCoordinate, simplexOfOrderedCoordinates] <;> ring

/-- A finite vertex type: three ordered integers between zero and n. -/
abbrev OrderedGridVertex (n : ℕ) :=
  {v : Fin 3 → Fin (n+1) // (v 0).val ≤ (v 1).val ∧ (v 1).val ≤ (v 2).val}

def gridVertexCoordinate (n : ℕ) (v : OrderedGridVertex n) (j : Fin 3) : ℝ :=
  ((v.val j).val : ℝ)/n

def gridVertexPosition (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n) : TetrahedralSimplex := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  refine simplexOfOrderedCoordinates (gridVertexCoordinate n v) (div_nonneg (Nat.cast_nonneg _) (le_of_lt hN)) ?_ ?_ ?_
  · apply div_le_div_of_nonneg_right _ (le_of_lt hN)
    exact_mod_cast v.property.1
  · apply div_le_div_of_nonneg_right _ (le_of_lt hN)
    exact_mod_cast v.property.2
  · apply (div_le_one hN).mpr
    have h := (v.val 2).isLt
    have h' : (v.val 2).val ≤ n := by omega
    exact_mod_cast h'

theorem gridVertexPosition_cumulative (n : ℕ) (hn : 0 < n)
    (v : OrderedGridVertex n) (j : Fin 3) :
    cumulativeCoordinate (gridVertexPosition n hn v) j = gridVertexCoordinate n v j := by
  unfold gridVertexPosition
  exact orderedCoordinates_cumulative _ _ _ _ _ j

/-- Convert every chain vertex to an index of the finite vertex table. -/
theorem located_grid_vertices (n : ℕ) (hn : 0 < n) (y : Fin 3 → ℝ) (o : Fin 6)
    (ho : ∀ t, gridCubeVertex n (fun j => gridBase n (y j)) o t 0 ≤
        gridCubeVertex n (fun j => gridBase n (y j)) o t 1 ∧
      gridCubeVertex n (fun j => gridBase n (y j)) o t 1 ≤
        gridCubeVertex n (fun j => gridBase n (y j)) o t 2) :
    ∃ v : Fin 4 → OrderedGridVertex n, ∀ t j, gridVertexCoordinate n (v t) j =
      gridCubeVertex n (fun j => gridBase n (y j)) o t j := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  choose raw hb he using fun t => located_vertex_integral n hn y o t
  have hord (t : Fin 4) : raw t 0 ≤ raw t 1 ∧ raw t 1 ≤ raw t 2 := by
    have h := ho t
    rw [he t 0, he t 1, he t 2] at h
    constructor
    · have hh := (div_le_div_iff_of_pos_right hN).mp h.1
      exact_mod_cast hh
    · have hh := (div_le_div_iff_of_pos_right hN).mp h.2
      exact_mod_cast hh
  let v : Fin 4 → OrderedGridVertex n := fun t =>
    ⟨fun j => ⟨raw t j, Nat.lt_succ_iff.mpr (hb t j)⟩, hord t⟩
  refine ⟨v, ?_⟩
  intro t j
  exact (he t j).symm

/-- Every parameter point is reconstructed by four actual finite grid vertices
of one located ordered chain. The statement holds for every positive n. -/
theorem tetrahedral_grid_cover (n : ℕ) (hn : 0 < n) (x : TetrahedralSimplex) :
    ∃ o : Fin 6, ∃ v : Fin 4 → OrderedGridVertex n, ∃ a : Fin 4 → ℝ,
      (∀ t, 0 ≤ a t) ∧ (∑ t, a t = 1) ∧
      (∀ t j, gridVertexCoordinate n (v t) j =
        gridCubeVertex n (fun j => gridBase n (cumulativeCoordinate x j)) o t j) ∧
      (∀ k, ∑ t, a t * (gridVertexPosition n hn (v t)).val k = x.val k) := by
  have hc := cumulativeCoordinate_ordered x
  obtain ⟨o, a, ha, hs, hr, ho, _⟩ := ordered_unit_grid_cover n hn (cumulativeCoordinate x)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  obtain ⟨v, hv⟩ := located_grid_vertices n hn (cumulativeCoordinate x) o ho
  have hrec (j : Fin 3) : ∑ t, a t * gridVertexCoordinate n (v t) j = cumulativeCoordinate x j := by
    simp_rw [hv]
    exact hr j
  refine ⟨o, v, a, ha, hs, hv, ?_⟩
  intro k
  fin_cases k
  · change (∑ t, a t * gridVertexCoordinate n (v t) 0) = x.val 0
    exact hrec 0
  · change (∑ t, a t * (gridVertexCoordinate n (v t) 1-gridVertexCoordinate n (v t) 0)) = x.val 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hrec 1, hrec 0]
    dsimp [cumulativeCoordinate]
    ring
  · change (∑ t, a t * (gridVertexCoordinate n (v t) 2-gridVertexCoordinate n (v t) 1)) = x.val 2
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hrec 2, hrec 1]
    dsimp [cumulativeCoordinate]
    ring
  · change (∑ t, a t * (1-gridVertexCoordinate n (v t) 2)) = x.val 3
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hs, hrec 2]
    have hsum : x.val 0+x.val 1+x.val 2+x.val 3 = 1 := by
      simpa [Fin.sum_univ_four, add_assoc] using x.property.2
    dsimp [cumulativeCoordinate]
    linarith

/-- Distinct finite table indices give distinct parameter points. -/
theorem gridVertexPosition_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (gridVertexPosition n hn) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  intro v w he
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hh := congrArg (fun x => cumulativeCoordinate x j) he
  rw [gridVertexPosition_cumulative, gridVertexPosition_cumulative] at hh
  have hc : ((v.val j).val : ℝ) = (w.val j).val :=
    (div_left_inj' (ne_of_gt hN)).mp hh
  exact_mod_cast hc

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
