import Foundation.Crypto.Semantics.Probability.ClassicalBitProjectiveInterpolation
import Mathlib.Topology.Homeomorph.Lemmas

/-! A finite simplicial realization is compact. A bijective geometric
projection therefore supplies continuous global barycentric coordinates.
The geometric cover and uniqueness obligations remain explicit. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
variable {Vertex : Type*} [Fintype Vertex]

theorem realizationSet_closed (K : PreAbstractSimplicialComplex Vertex) :
    IsClosed (realizationSet K) := by
  classical
  let Faces := {cell : Finset Vertex // cell ∈ K}
  have heq : realizationSet K = stdSimplex ℝ Vertex ∩
      ⋃ cell : Faces, {w : Vertex → ℝ | ∀ i, i ∉ cell.val → w i = 0} := by
    ext w
    simp only [realizationSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨ha, hs, cell, hc, ht⟩
      refine ⟨⟨ha, hs⟩, ⟨cell, hc⟩, ?_⟩
      intro i hi
      by_contra hn
      exact hi (ht i hn)
    · rintro ⟨⟨ha, hs⟩, cell, ht⟩
      refine ⟨ha, hs, cell.val, cell.property, ?_⟩
      intro i hi
      by_contra hn
      exact hi (ht i hn)
  rw [heq]
  apply (isClosed_stdSimplex ℝ Vertex).inter
  apply isClosed_iUnion_of_finite
  intro cell
  have heq' : {w : Vertex → ℝ | ∀ i, i ∉ cell.val → w i = 0} =
      ⋂ i, ⋂ (_ : i ∉ cell.val), {w : Vertex → ℝ | w i = 0} := by ext; simp
  rw [heq']
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

theorem realizationSet_compact (K : PreAbstractSimplicialComplex Vertex) :
    IsCompact (realizationSet K) :=
  (isCompact_stdSimplex ℝ Vertex).of_isClosed_subset (realizationSet_closed K)
    (fun _ h => ⟨h.1, h.2.1⟩)

instance realizationCompactSpace (K : PreAbstractSimplicialComplex Vertex) :
    CompactSpace (Realization K) :=
  isCompact_iff_compactSpace.mp (realizationSet_compact K)

/-- The geometric projection uses vertex positions, independently of cipher labels. -/
def meshProjection (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) : C(Realization K, TetrahedralSimplex) where
  toFun w := ⟨fun k => ∑ i, w.val i * (p i).val k, by
    constructor
    · intro k
      exact Finset.sum_nonneg fun i _ => mul_nonneg (w.property.1 i) ((p i).property.1 k)
    · rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (p _).property.2, mul_one]
      exact w.property.2.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

def meshHomeomorph (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p)) :
    Realization K ≃ₜ TetrahedralSimplex :=
  ((isHomeomorph_iff_continuous_bijective).mpr ⟨(meshProjection K p).continuous, h⟩).homeomorph _

def meshWeight (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (i : Vertex) : C(TetrahedralSimplex, ℝ) where
  toFun x := (meshHomeomorph K p h).symm x |>.val i
  continuous_toFun := (continuous_apply i).comp
    (continuous_subtype_val.comp (meshHomeomorph K p h).symm.continuous)

theorem meshWeight_nonneg (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (x : TetrahedralSimplex) (i : Vertex) : 0 ≤ meshWeight K p h i x :=
  ((meshHomeomorph K p h).symm x).property.1 i

theorem meshWeight_sum (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (x : TetrahedralSimplex) : ∑ i, meshWeight K p h i x = 1 :=
  ((meshHomeomorph K p h).symm x).property.2.1

theorem meshWeight_reconstruct (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (x : TetrahedralSimplex) (k : Fin 4) :
    ∑ i, meshWeight K p h i x * (p i).val k = x.val k := by
  have hx := (meshHomeomorph K p h).apply_symm_apply x
  exact congrFun (congrArg Subtype.val hx) k

theorem meshWeight_support (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (x : TetrahedralSimplex) :
    ∃ cell ∈ K, ∀ i, meshWeight K p h i x ≠ 0 → i ∈ cell :=
  ((meshHomeomorph K p h).symm x).property.2.2

/-- No continuous weights or pointwise boundary witnesses are supplied. -/
theorem mesh_projective_forces_zero (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (q : Vertex → Fin 4 → ℝ) (hq : ∀ i, bias (q i) = 0)
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (q i) (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ x, projectiveInterpolation (meshWeight K p h) p q
      (meshWeight_nonneg K p h) (meshWeight_sum K p h) x = 0 :=
  projectiveInterpolation_forces_zero _ p q (meshWeight_nonneg K p h)
    (meshWeight_sum K p h) (meshWeight_reconstruct K p h) hq he

/-- Reweighting preserves membership in the same abstract face. -/
def projectiveRealization (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (w : Realization K) : Realization K := by
  let D := projectiveDenominator w.val p
  have hd : 0 < D := by
    have hh := projectiveDenominator_lower w.val p w.property.1 w.property.2.1
    dsimp [D]; linarith
  refine ⟨fun i => w.val i * projectiveScale (p i) / D, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (mul_nonneg (w.property.1 i)
      (le_trans (by norm_num) (le_max_right _ _))) (le_of_lt hd)
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hd)
  · obtain ⟨cell, hc, ht⟩ := w.property.2.2
    refine ⟨cell, hc, ?_⟩
    intro i hi
    apply ht i
    intro hz
    apply hi
    simp [hz]

theorem projectiveMixture_cell (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (q : Vertex → Fin 4 → ℝ) (w : Realization K) :
    ∃ cell ∈ K, projectiveMixture w.val p q ∈ convexHull ℝ (q '' (cell : Set Vertex)) :=
  interpolate_cell K q (projectiveRealization K p w)

/-- The zero lies inside a single cell, so its jump is on an actual mesh edge. -/
theorem mesh_projective_perfect_edge (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (d : Vertex → PerfectCipher (Fin 4))
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (d i).signed (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨x, hx⟩ := mesh_projective_forces_zero K p h (fun i => (d i).signed)
    (fun i => (d i).bias_zero) he
  obtain ⟨cell, hc, hmix⟩ := projectiveMixture_cell K p (fun i => (d i).signed)
    ((meshHomeomorph K p h).symm x)
  change projectiveMixture (fun i => meshWeight K p h i x) p (fun i => (d i).signed) ∈ _ at hmix
  change projectiveMixture (fun i => meshWeight K p h i x) p (fun i => (d i).signed) = 0 at hx
  rw [hx] at hmix
  obtain ⟨u, _, v, _, hedge, htv⟩ := perfect_cell_edge_jump d (cell : Set Vertex)
    (faceEdge K) (fun u hu v hv hne => ⟨hne, cell, hc, hu, hv⟩) hmix
  exact ⟨u, v, hedge, htv⟩

/-- The same geometric construction also certifies the approximate cipher
bound; the boundary certificates apply to the repaired signed contrasts. -/
theorem mesh_projective_approximate_edge (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (h : Function.Bijective (meshProjection K p))
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (repair (signedContrast (c i)))
        (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  let q := fun i => repair (signedContrast (c i))
  have hq (i : Vertex) : bias (q i) = 0 := by
    have hmargin := repair_margin_bound (c i) (ε i) (δ i) μ (h0 i) (h1 i) (hp i) (hm i)
    apply repair_bias <;> linarith [hmargin.1, hmargin.2]
  obtain ⟨x, hx⟩ := mesh_projective_forces_zero K p h q hq he
  obtain ⟨cell, hc, hmix⟩ := projectiveMixture_cell K p q ((meshHomeomorph K p h).symm x)
  change projectiveMixture (fun i => meshWeight K p h i x) p q ∈ _ at hmix
  change projectiveMixture (fun i => meshWeight K p h i x) p q = 0 at hx
  rw [hx] at hmix
  obtain ⟨u, _, v, _, hedge, hd⟩ := approximate_cell_edge_jump c (cell : Set Vertex)
    (faceEdge K) (fun u hu v hv hne => ⟨hne, cell, hc, hu, hv⟩) ε δ μ hμ
    (fun i _ => h0 i) (fun i _ => h1 i) (fun i _ => hp i) (fun i _ => hm i) hmix
  exact ⟨u, v, hedge, hd⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
