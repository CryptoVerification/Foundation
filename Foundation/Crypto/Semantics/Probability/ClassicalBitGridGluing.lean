import Foundation.Crypto.Semantics.Probability.ClassicalBitIntegralChain

/-! Common-face gluing for the complete ordered grid, including different
base cubes. Integer width-one inequalities transfer through equal means. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

theorem supported_image_width {Vertex : Type*} [DecidableEq Vertex]
    (v : Fin 4 → Vertex) (a : Vertex → ℝ) (f : Vertex → ℤ)
    (ht : ∀ i, a i ≠ 0 → i ∈ Finset.univ.image v)
    (hw : ∀ s t, f (v s) ≤ f (v t)+1) :
    ∀ i, a i ≠ 0 → ∀ j, a j ≠ 0 → f i ≤ f j+1 := by
  intro i hi j hj
  obtain ⟨s, _, hsi⟩ := Finset.mem_image.mp (ht i hi)
  obtain ⟨t, _, htj⟩ := Finset.mem_image.mp (ht j hj)
  rw [← hsi, ← htj]
  exact hw s t

theorem grid_integer_means_eq (n : ℕ) (hn : 0 < n)
    (a b : OrderedGridVertex n → ℝ)
    (he : (∑ i, a i • (gridVertexPosition n hn i).val) =
      ∑ i, b i • (gridVertexPosition n hn i).val) (j : Fin 3) :
    (∑ i, a i * (gridIntegralCoordinate i j : ℝ)) =
      ∑ i, b i * (gridIntegralCoordinate i j : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := congrArg cumulativeLinear he
  simp only [map_sum, map_smul] at hc
  have hh := congrFun hc j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    cumulativeLinear_gridVertex, gridVertexCoordinate] at hh
  simp_rw [← mul_div_assoc] at hh
  rw [← Finset.sum_div, ← Finset.sum_div] at hh
  have hk := (div_left_inj' (ne_of_gt hN)).mp hh
  simpa only [gridIntegralCoordinate, Int.cast_natCast] using hk

/-- Equal integer-coordinate means force every active vertex of the second
chain into the first chain. The two base cubes need not coincide. -/
theorem grid_chain_support_transfer (n : ℕ) (hn : 0 < n)
    (baseA baseB : Fin 3 → Fin n) (oA oB : Fin 6)
    (vA vB : Fin 4 → OrderedGridVertex n)
    (hvA : gridChain n baseA oA vA) (hvB : gridChain n baseB oB vB)
    (a b : OrderedGridVertex n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 1)
    (hta : ∀ i, a i ≠ 0 → i ∈ Finset.univ.image vA)
    (htb : ∀ i, b i ≠ 0 → i ∈ Finset.univ.image vB)
    (hm : ∀ j, (∑ i, a i * (gridIntegralCoordinate i j : ℝ)) =
      ∑ i, b i * (gridIntegralCoordinate i j : ℝ)) :
    ∀ i, b i ≠ 0 → i ∈ Finset.univ.image vA := by
  intro i hi
  have haBox (w : OrderedGridVertex n) (hw : a w ≠ 0) (j : Fin 3) :
      ((baseA j).val : ℤ) ≤ gridIntegralCoordinate w j ∧
        gridIntegralCoordinate w j ≤ ((baseA j).val : ℤ)+1 := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hta w hw)
    rw [← ht]
    have he := gridChain_integral_coordinate n hn baseA oA vA hvA t j
    have hc := cubeVertex_bounds oA t j
    constructor
    · have hh : ((baseA j).val : ℝ) ≤ (gridIntegralCoordinate (vA t) j : ℝ) := by
        rw [he]; linarith
      exact_mod_cast hh
    · have hh : (gridIntegralCoordinate (vA t) j : ℝ) ≤ ((baseA j).val : ℝ)+1 := by
        rw [he]; linarith
      exact_mod_cast hh
  have hbox (j : Fin 3) : ((baseA j).val : ℤ) ≤ gridIntegralCoordinate i j ∧
      gridIntegralCoordinate i j ≤ ((baseA j).val : ℤ)+1 := by
    have hlo := integral_average_ge a (fun w => gridIntegralCoordinate w j)
      ((baseA j).val : ℤ) ha hsa (fun w hw => (haBox w hw j).1)
    have hhi := integral_average_le a (fun w => gridIntegralCoordinate w j)
      (((baseA j).val : ℤ)+1) ha hsa (fun w hw => (haBox w hw j).2)
    rw [hm j] at hlo hhi
    have hw := supported_image_width vB b (fun w => gridIntegralCoordinate w j) htb
      (fun s t => gridChain_coordinate_width n hn baseB oB vB hvB s t j)
    exact ⟨integral_support_ge b _ _ hb hsb hw hlo i hi,
      integral_support_le b _ _ hb hsb hw hhi i hi⟩
  have horder (r s : Fin 3) (hc : ∀ t, cubeVertex oA t r ≤ cubeVertex oA t s) :
      gridIntegralCoordinate i r-gridIntegralCoordinate i s ≤
        ((baseA r).val : ℤ)-((baseA s).val : ℤ) := by
    let f := fun w : OrderedGridVertex n => gridIntegralCoordinate w r-gridIntegralCoordinate w s
    let K : ℤ := ((baseA r).val : ℤ)-((baseA s).val : ℤ)
    have hf (w : OrderedGridVertex n) (hw : a w ≠ 0) : f w ≤ K := by
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hta w hw)
      rw [← ht]
      have hreal : (f (vA t) : ℝ) ≤ (K : ℝ) := by
        dsimp [f, K]
        push_cast
        rw [gridChain_integral_coordinate n hn baseA oA vA hvA,
          gridChain_integral_coordinate n hn baseA oA vA hvA]
        linarith [hc t]
      exact_mod_cast hreal
    have hma := integral_average_le a f K ha hsa hf
    have hmf : (∑ w, a w * (f w : ℝ)) = ∑ w, b w * (f w : ℝ) := by
      simp only [f, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
      rw [hm r, hm s]
    rw [hmf] at hma
    have hw := supported_image_width vB b f htb
      (fun u v => gridChain_difference_width n hn baseB oB vB hvB u v r s)
    exact integral_support_le b f K hb hsb hw hma i hi
  have h21 := horder (cubeAxisOrder oA 2) (cubeAxisOrder oA 1)
    (fun t => (cubeVertex_sorted oA t).1)
  have h10 := horder (cubeAxisOrder oA 1) (cubeAxisOrder oA 0)
    (fun t => (cubeVertex_sorted oA t).2)
  have hc21 : ((gridIntegralCoordinate i (cubeAxisOrder oA 2) : ℝ)-
      (gridIntegralCoordinate i (cubeAxisOrder oA 1) : ℝ)) ≤
      (((baseA (cubeAxisOrder oA 2)).val : ℝ)-((baseA (cubeAxisOrder oA 1)).val : ℝ)) := by
    exact_mod_cast h21
  have hc10 : ((gridIntegralCoordinate i (cubeAxisOrder oA 1) : ℝ)-
      (gridIntegralCoordinate i (cubeAxisOrder oA 0) : ℝ)) ≤
      (((baseA (cubeAxisOrder oA 1)).val : ℝ)-((baseA (cubeAxisOrder oA 0)).val : ℝ)) := by
    exact_mod_cast h10
  apply gridChain_region_member n hn baseA oA vA hvA i hbox
  constructor <;> linarith

/-- The concrete common-face condition, including chains in distinct cubes. -/
theorem orderedGridComplex_common_face (n : ℕ) (hn : 0 < n)
    (s : Finset (OrderedGridVertex n)) (hs : s ∈ orderedGridComplex n)
    (t : Finset (OrderedGridVertex n)) (ht : t ∈ orderedGridComplex n) :
    convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) '' (s : Set (OrderedGridVertex n))) ∩
      convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) '' (t : Set (OrderedGridVertex n))) ⊆
      convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) ''
        ((s : Set (OrderedGridVertex n)) ∩ (t : Set (OrderedGridVertex n)))) := by
  classical
  intro x hx
  let p := fun i : OrderedGridVertex n => (gridVertexPosition n hn i).val
  have hp : Function.Injective p := fun _ _ he => gridVertexPosition_injective n hn (Subtype.ext he)
  obtain ⟨a, ha, hsa, hta, hax⟩ := face_weights_of_mem_convexHull p hp s x hx.1
  obtain ⟨b, hb, hsb, htb, hbx⟩ := face_weights_of_mem_convexHull p hp t x hx.2
  obtain ⟨_, baseA, oA, vA, hvA, hsubA⟩ := hs
  obtain ⟨_, baseB, oB, vB, hvB, hsubB⟩ := ht
  have hactiveA (i : OrderedGridVertex n) (hi : a i ≠ 0) : i ∈ Finset.univ.image vA := by
    apply hsubA
    by_contra h
    exact hi (hta i h)
  have hactiveB (i : OrderedGridVertex n) (hi : b i ≠ 0) : i ∈ Finset.univ.image vB := by
    apply hsubB
    by_contra h
    exact hi (htb i h)
  have he : (∑ i, a i • (gridVertexPosition n hn i).val) =
      ∑ i, b i • (gridVertexPosition n hn i).val := hax.trans hbx.symm
  have htransfer := grid_chain_support_transfer n hn baseA baseB oA oB vA vB hvA hvB
    a b ha hb hsa hsb hactiveA hactiveB (grid_integer_means_eq n hn a b he)
  have houtA (i : OrderedGridVertex n) (hi : i ∉ Finset.univ.image vA) : a i = 0 := by
    by_contra h
    exact hi (hactiveA i h)
  have houtB (i : OrderedGridVertex n) (hi : i ∉ Finset.univ.image vA) : b i = 0 := by
    by_contra h
    exact hi (htransfer i h)
  have hcell : Finset.univ.image vA ∈ orderedGridComplex n :=
    ⟨Finset.image_nonempty.mpr Finset.univ_nonempty, baseA, oA, vA, hvA, Finset.Subset.refl _⟩
  have hab := face_weights_unique p (Finset.univ.image vA)
    (orderedGridComplex_independent n hn _ hcell) a b hsa hsb houtA houtB he
  have hout (i : OrderedGridVertex n) (hi : i ∉ s ∩ t) : a i = 0 := by
    by_cases his : i ∈ s
    · have hit : i ∉ t := fun h => hi (Finset.mem_inter.mpr ⟨his, h⟩)
      rw [hab]
      exact htb i hit
    · exact hta i his
  have hmem := supported_weights_mem_convexHull p (s ∩ t) a ha hsa hout
  rw [hax] at hmem
  simpa only [Finset.coe_inter] using hmem

/-- The concrete ordered grid now satisfies every geometric obligation. -/
theorem orderedGridComplex_meshGeometry (n : ℕ) (hn : 0 < n) :
    MeshGeometry (orderedGridComplex n) (gridVertexPosition n hn) :=
  orderedGridComplex_geometry n hn (orderedGridComplex_common_face n hn)

theorem ordered_grid_perfect_edge (n : ℕ) (hn : 0 < n)
    (d : OrderedGridVertex n → PerfectCipher (Fin 4))
    (he : ∀ i, (∃ k, (gridVertexPosition n hn i).val k = 0) →
      l1Distance (d i).signed (normalizeSigned (sharpAffine (gridVertexPosition n hn i))) ≤ 1 / 64) :
    ∃ u v, faceEdge (orderedGridComplex n) u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message :=
  geometric_mesh_perfect_edge (orderedGridComplex n) (gridVertexPosition n hn)
    (orderedGridComplex_meshGeometry n hn) d he

theorem orderedGridComplex_projection_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (meshProjection (orderedGridComplex n) (gridVertexPosition n hn)) :=
  meshGeometry_projection_bijective _ _ (orderedGridComplex_meshGeometry n hn)

/-- Every concrete ordered grid has continuous, normalized, reconstructing
coordinates supported in a single actual grid face. -/
theorem ordered_grid_weights_exist (n : ℕ) (hn : 0 < n) :
    ∃ a : OrderedGridVertex n → C(TetrahedralSimplex, ℝ),
      (∀ x i, 0 ≤ a i x) ∧ (∀ x, ∑ i, a i x = 1) ∧
      (∀ x k, ∑ i, a i x * (gridVertexPosition n hn i).val k = x.val k) ∧
      (∀ x, ∃ cell ∈ orderedGridComplex n, ∀ i, a i x ≠ 0 → i ∈ cell) := by
  let h := orderedGridComplex_projection_bijective n hn
  exact ⟨meshWeight _ _ h, meshWeight_nonneg _ _ h, meshWeight_sum _ _ h,
    meshWeight_reconstruct _ _ h, meshWeight_support _ _ h⟩

theorem ordered_grid_approximate_edge (n : ℕ) (hn : 0 < n)
    (c : OrderedGridVertex n → Cipher (Fin 4)) (ε δ : OrderedGridVertex n → ℝ)
    (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i+2*δ i ≤ 1-μ)
    (he : ∀ i, (∃ k, (gridVertexPosition n hn i).val k = 0) →
      l1Distance (repair (signedContrast (c i)))
        (normalizeSigned (sharpAffine (gridVertexPosition n hn i))) ≤ 1 / 64) :
    ∃ u v, faceEdge (orderedGridComplex n) u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) :=
  geometric_mesh_approximate_edge (orderedGridComplex n) (gridVertexPosition n hn)
    (orderedGridComplex_meshGeometry n hn) c ε δ μ hμ h0 h1 hp hm he

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
