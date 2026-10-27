import Foundation.Crypto.Semantics.Probability.ClassicalBitGridLocator

/-! The finite ordered grid complex, its all-point cover, and affine
independence of every face. Global common-face gluing remains separate. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

def gridChain (n : ℕ) (base : Fin 3 → Fin n) (o : Fin 6)
    (v : Fin 4 → OrderedGridVertex n) : Prop :=
  ∀ t j, gridVertexCoordinate n (v t) j =
    gridCubeVertex n (fun j => ((base j).val : ℝ)) o t j

/-- Include precisely all nonempty subsets of valid ordered grid chains. -/
def orderedGridComplex (n : ℕ) : PreAbstractSimplicialComplex (OrderedGridVertex n) where
  faces := {cell | cell.Nonempty ∧ ∃ base : Fin 3 → Fin n, ∃ o : Fin 6,
    ∃ v : Fin 4 → OrderedGridVertex n, gridChain n base o v ∧ cell ⊆ Finset.univ.image v}
  isRelLowerSet_faces := by
    intro cell hc
    refine ⟨hc.1, ?_⟩
    intro face hsub hne
    obtain ⟨base, o, v, hv, hs⟩ := hc.2
    exact ⟨hne, base, o, v, hv, hsub.trans hs⟩

def cumulativeLinear : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x j := if j.val = 0 then x 0 else if j.val = 1 then x 0+x 1 else x 0+x 1+x 2
  map_add' x y := by funext j; fin_cases j <;> dsimp <;> ring
  map_smul' a x := by funext j; fin_cases j <;> dsimp <;> ring

theorem cumulativeLinear_gridVertex (n : ℕ) (hn : 0 < n) (v : OrderedGridVertex n) :
    cumulativeLinear (gridVertexPosition n hn v).val = gridVertexCoordinate n v := by
  funext j
  exact gridVertexPosition_cumulative n hn v j

/-- The inverse affine change of coordinates sends any valid chain back to
the unit-cube chain, whose affine independence has already been proved. -/
theorem gridChain_affineIndependent (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v) :
    AffineIndependent ℝ (fun t => (gridVertexPosition n hn (v t)).val) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  let b : Fin 3 → ℝ := fun j => (base j).val
  let f : (Fin 4 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
    (n : ℝ) • cumulativeLinear.toAffineMap - AffineMap.const ℝ (Fin 4 → ℝ) b
  have heq : f ∘ (fun t => (gridVertexPosition n hn (v t)).val) = cubeVertex o := by
    funext t j
    change (n : ℝ) * cumulativeLinear (gridVertexPosition n hn (v t)).val j-b j = _
    rw [cumulativeLinear_gridVertex, hv t j]
    dsimp [gridCubeVertex, b]
    field_simp [ne_of_gt hN]
    ring
  apply AffineIndependent.of_comp f
  rw [heq]
  exact cube_chain_affineIndependent o

theorem gridChain_injective (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v) :
    Function.Injective v := by
  intro s t hst
  apply (gridChain_affineIndependent n hn base o v hv).injective
  exact congrArg (fun i => (gridVertexPosition n hn i).val) hst

theorem gridChain_card (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v) :
    (Finset.univ.image v).card = 4 := by
  rw [Finset.card_image_of_injective _ (gridChain_injective n hn base o v hv)]
  simp

/-- Every face inherits independence from its containing four-vertex chain. -/
theorem orderedGridComplex_independent (n : ℕ) (hn : 0 < n)
    (cell : Finset (OrderedGridVertex n)) (hc : cell ∈ orderedGridComplex n) :
    AffineIndependent ℝ (fun i : cell => (gridVertexPosition n hn i).val) := by
  classical
  obtain ⟨_, base, o, v, hv, hs⟩ := hc
  have hidx (i : cell) : ∃ t : Fin 4, v t = i.val := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hs i.property)
    exact ⟨t, ht⟩
  choose idx hidx using hidx
  let e : cell ↪ Fin 4 := ⟨idx, by
    intro i j hij
    apply Subtype.ext
    rw [← hidx i, ← hidx j, hij]⟩
  have hi := (gridChain_affineIndependent n hn base o v hv).comp_embedding e
  change AffineIndependent ℝ (fun i : cell => (gridVertexPosition n hn (v (idx i))).val) at hi
  simp_rw [hidx] at hi
  exact hi

theorem orderedGridComplex_cover (n : ℕ) (hn : 0 < n) (x : TetrahedralSimplex) :
    ∃ cell ∈ orderedGridComplex n, x.val ∈ convexHull ℝ
      ((fun i => (gridVertexPosition n hn i).val) '' (cell : Set (OrderedGridVertex n))) := by
  classical
  obtain ⟨o, v, a, ha, hs, hv, hr⟩ := tetrahedral_grid_cover n hn x
  let base : Fin 3 → Fin n := fun j =>
    ⟨gridBase n (cumulativeCoordinate x j), gridBase_lt n hn _⟩
  let cell := Finset.univ.image v
  have hc : cell ∈ orderedGridComplex n := by
    refine ⟨Finset.image_nonempty.mpr Finset.univ_nonempty, base, o, v, hv, ?_⟩
    exact Finset.Subset.refl _
  refine ⟨cell, hc, ?_⟩
  apply mem_convexHull_of_exists_fintype a (fun t => (gridVertexPosition n hn (v t)).val) ha hs
  · intro t
    exact ⟨v t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, rfl⟩
  · funext k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hr k

/-- All MeshGeometry fields except the explicitly retained common-face
condition are now consequences of the concrete grid construction. -/
theorem orderedGridComplex_geometry (n : ℕ) (hn : 0 < n)
    (hcommon : ∀ s ∈ orderedGridComplex n, ∀ t ∈ orderedGridComplex n,
      convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) '' (s : Set (OrderedGridVertex n))) ∩
        convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) '' (t : Set (OrderedGridVertex n))) ⊆
        convexHull ℝ ((fun i => (gridVertexPosition n hn i).val) ''
          ((s : Set (OrderedGridVertex n)) ∩ (t : Set (OrderedGridVertex n))))) :
    MeshGeometry (orderedGridComplex n) (gridVertexPosition n hn) where
  distinct := fun _i _j hij => gridVertexPosition_injective n hn (Subtype.ext hij)
  independent := orderedGridComplex_independent n hn
  common_face := hcommon
  cover := orderedGridComplex_cover n hn

theorem orderedGridComplex_card (n : ℕ) (hn : 0 < n)
    (cell : Finset (OrderedGridVertex n)) (hc : cell ∈ orderedGridComplex n) : cell.card ≤ 4 := by
  obtain ⟨_, base, o, v, hv, hs⟩ := hc
  calc
    cell.card ≤ (Finset.univ.image v).card := Finset.card_le_card hs
    _ = 4 := gridChain_card n hn base o v hv

/-- The mesh edges are precisely pairs appearing in a single valid chain;
there is no substitution of the complete graph on all finite vertices. -/
theorem orderedGridComplex_edge_iff (n : ℕ) (u w : OrderedGridVertex n) :
    faceEdge (orderedGridComplex n) u w ↔ u ≠ w ∧
      ∃ base : Fin 3 → Fin n, ∃ o : Fin 6, ∃ v : Fin 4 → OrderedGridVertex n,
        gridChain n base o v ∧ u ∈ Finset.univ.image v ∧ w ∈ Finset.univ.image v := by
  classical
  constructor
  · rintro ⟨hne, cell, hc, hu, hw⟩
    obtain ⟨_, base, o, v, hv, hs⟩ := hc
    exact ⟨hne, base, o, v, hv, hs hu, hs hw⟩
  · rintro ⟨hne, base, o, v, hv, hu, hw⟩
    refine ⟨hne, Finset.univ.image v, ?_, hu, hw⟩
    exact ⟨Finset.image_nonempty.mpr Finset.univ_nonempty, base, o, v, hv, Finset.Subset.refl _⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
