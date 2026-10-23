import Foundation.Crypto.Semantics.Probability.ClassicalBitBoundaryCertificate

/-! A canonical finite barycentric realization and its cipher interpolation.
Continuity, zero-sum preservation, and the single-cell cover are derived from
coordinates and abstract faces, rather than supplied as opaque premises. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Vertex Key : Type*} [Fintype Vertex]

def realizationSet (K : PreAbstractSimplicialComplex Vertex) : Set (Vertex → ℝ) :=
  {w | (∀ v, 0 ≤ w v) ∧ (∑ v, w v) = 1 ∧
    ∃ cell ∈ K, ∀ v, w v ≠ 0 → v ∈ cell}

abbrev Realization (K : PreAbstractSimplicialComplex Vertex) := ↥(realizationSet K)

def faceEdge (K : PreAbstractSimplicialComplex Vertex) (u v : Vertex) : Prop :=
  u ≠ v ∧ ∃ cell ∈ K, u ∈ cell ∧ v ∈ cell

def interpolate (K : PreAbstractSimplicialComplex Vertex) (label : Vertex → Key → ℝ) :
    C(Realization K, Key → ℝ) where
  toFun x := ∑ v, x.val v • label v
  continuous_toFun := continuous_finsetSum _ fun v _ =>
    ((continuous_apply v).comp continuous_subtype_val).smul continuous_const

def vertexPoint (K : PreAbstractSimplicialComplex Vertex) (v : Vertex)
    (hv : {v} ∈ K) : Realization K := by
    classical
    refine ⟨fun i => if i = v then 1 else 0, ?_⟩
    refine ⟨?_, ?_, {v}, hv, ?_⟩
    · intro i
      dsimp
      split_ifs <;> norm_num
    · simp
    · intro i hi
      by_cases h : i = v
      · simp [h]
      · simp [h] at hi

theorem interpolate_vertex (K : PreAbstractSimplicialComplex Vertex)
    (label : Vertex → Key → ℝ) (v : Vertex) (hv : {v} ∈ K) :
    interpolate K label (vertexPoint K v hv) = label v := by
  classical
  simp [interpolate, vertexPoint]

theorem interpolate_bias [Fintype Key] (K : PreAbstractSimplicialComplex Vertex)
    (label : Vertex → Key → ℝ) (hz : ∀ v, bias (label v) = 0) (x : Realization K) :
    bias (interpolate K label x) = 0 := by
  change (∑ k, (∑ v, x.val v • label v) k) = 0
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ v, x.val v * bias (label v)) = 0
  simp_rw [hz, mul_zero]
  simp

theorem interpolate_cell (K : PreAbstractSimplicialComplex Vertex)
    (label : Vertex → Key → ℝ) (x : Realization K) :
    ∃ cell ∈ K, interpolate K label x ∈ convexHull ℝ (label '' (cell : Set Vertex)) := by
  classical
  obtain ⟨cell, hcell, hsupport⟩ := x.property.2.2
  have hout (i : Vertex) (hi : i ∉ cell) : x.val i = 0 := by
    by_contra h
    exact hi (hsupport i h)
  have hsum : (∑ i ∈ cell, x.val i) = 1 := by
    calc
      _ = ∑ i, x.val i := Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => hout i hi)
      _ = 1 := x.property.2.1
  have hcomb : (∑ i ∈ cell, x.val i • label i) = interpolate K label x := by
    change (∑ i ∈ cell, x.val i • label i) = ∑ i, x.val i • label i
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [hout i hi, zero_smul]
  have hsum' : (∑ i : cell, x.val i) = 1 := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
  have hcomb' : (∑ i : cell, x.val i • label i) = interpolate K label x := by
    rw [Finset.univ_eq_attach]
    change (∑ i ∈ cell.attach, (fun v : Vertex => x.val v • label v) i) = _
    rw [Finset.sum_attach (f := fun v : Vertex => x.val v • label v)]
    exact hcomb
  refine ⟨cell, hcell, mem_convexHull_of_exists_fintype
    (fun i : cell => x.val i) (fun i : cell => label i)
    (fun i => x.property.1 i) hsum' (fun i => ?_) hcomb'⟩
  exact ⟨i, i.property, rfl⟩

/-- Builds the exact cell-cover premise of the boundary theorem. -/
theorem interpolate_cover (K : PreAbstractSimplicialComplex Vertex)
    (label : Vertex → Key → ℝ) (x : Realization K) :
    ∃ cell : Set Vertex,
      (∀ u ∈ cell, ∀ v ∈ cell, u ≠ v → faceEdge K u v) ∧
      interpolate K label x ∈ convexHull ℝ (label '' cell) := by
  obtain ⟨cell, hcell, hx⟩ := interpolate_cell K label x
  refine ⟨cell, ?_, hx⟩
  intro u hu v hv hne
  exact ⟨hne, cell, hcell, hu, hv⟩

omit [Fintype Vertex] in
theorem faceEdge_iff_pair [DecidableEq Vertex] (K : PreAbstractSimplicialComplex Vertex)
    (u v : Vertex) : faceEdge K u v ↔ u ≠ v ∧ ({u, v} : Finset Vertex) ∈ K := by
  constructor
  · rintro ⟨hne, cell, hcell, hu, hv⟩
    refine ⟨hne, (K.isRelLowerSet_faces hcell).2 ?_ (Finset.insert_nonempty _ _)⟩
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hu, hv]
  · rintro ⟨hne, hpair⟩
    exact ⟨hne, {u, v}, hpair, by simp, by simp⟩

/-- A finite cone condition proves contractibility of the canonical realization. -/
theorem cone_realization_contractible [DecidableEq Vertex] (K : PreAbstractSimplicialComplex Vertex)
    (apex : Vertex) (hapex : {apex} ∈ K)
    (hcone : ∀ cell ∈ K, insert apex cell ∈ K) : ContractibleSpace (Realization K) := by
  classical
  let center := vertexPoint K apex hapex
  have hstar : StarConvex ℝ center.val (realizationSet K) := by
    intro y hy a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro v
      exact add_nonneg (mul_nonneg ha (center.property.1 v)) (mul_nonneg hb (hy.1 v))
    · change (∑ v, (a * center.val v + b * y v)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        center.property.2.1, hy.2.1]
      linarith
    · obtain ⟨cell, hcell, hsupport⟩ := hy.2.2
      refine ⟨insert apex cell, hcone cell hcell, ?_⟩
      intro v hv
      by_cases heq : v = apex
      · simp [heq]
      · apply Finset.mem_insert_of_mem
        apply hsupport
        intro hyzero
        apply hv
        simp [center, vertexPoint, heq, hyzero]
  exact hstar.contractibleSpace ⟨center.val, center.property⟩

theorem interpolated_perfect_edge {Boundary : Type*} [TopologicalSpace Boundary]
    (K : PreAbstractSimplicialComplex Vertex) [ContractibleSpace (Realization K)]
    (d : Vertex → PerfectCipher (Fin 4)) (boundary : C(Boundary, Realization K))
    (f : C(Boundary, PerfectVector (Fin 4))) (hnonnull : ¬f.Nullhomotopic)
    (hb : ∀ s, interpolate K (fun v => (d v).signed) (boundary s) = (f s).val) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  exact nonnull_boundary_forces_perfect_edge boundary f hnonnull
    (interpolate K (fun v => (d v).signed))
    (interpolate_bias K _ (fun v => (d v).bias_zero)) hb d (faceEdge K)
    (interpolate_cover K _)

theorem interpolated_approximate_edge {Boundary : Type*} [TopologicalSpace Boundary]
    (K : PreAbstractSimplicialComplex Vertex) [ContractibleSpace (Realization K)]
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (boundary : C(Boundary, Realization K)) (f : C(Boundary, PerfectVector (Fin 4)))
    (hnonnull : ¬f.Nullhomotopic)
    (hb : ∀ s, interpolate K (fun v => repair (signedContrast (c v))) (boundary s) = (f s).val) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have hmargin (i : Vertex) := repair_margin_bound (c i) (ε i) (δ i) μ
    (h0 i) (h1 i) (hp i) (hm i)
  have hz (i : Vertex) : bias (repair (signedContrast (c i))) = 0 := by
    apply repair_bias <;> linarith [(hmargin i).1, (hmargin i).2]
  exact nonnull_boundary_forces_approximate_edge boundary f hnonnull
    (interpolate K (fun v => repair (signedContrast (c v))))
    (interpolate_bias K _ hz) hb c (faceEdge K) ε δ μ hμ h0 h1 hp hm
    (interpolate_cover K _)

theorem cone_perfect_edge [DecidableEq Vertex] {Boundary : Type*} [TopologicalSpace Boundary]
    (K : PreAbstractSimplicialComplex Vertex) (apex : Vertex) (hapex : {apex} ∈ K)
    (hcone : ∀ cell ∈ K, insert apex cell ∈ K)
    (d : Vertex → PerfectCipher (Fin 4)) (boundary : C(Boundary, Realization K))
    (f : C(Boundary, PerfectVector (Fin 4))) (hnonnull : ¬f.Nullhomotopic)
    (hb : ∀ s, interpolate K (fun v => (d v).signed) (boundary s) = (f s).val) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  have := cone_realization_contractible K apex hapex hcone
  exact interpolated_perfect_edge K d boundary f hnonnull hb

theorem cone_approximate_edge [DecidableEq Vertex] {Boundary : Type*} [TopologicalSpace Boundary]
    (K : PreAbstractSimplicialComplex Vertex) (apex : Vertex) (hapex : {apex} ∈ K)
    (hcone : ∀ cell ∈ K, insert apex cell ∈ K)
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (boundary : C(Boundary, Realization K)) (f : C(Boundary, PerfectVector (Fin 4)))
    (hnonnull : ¬f.Nullhomotopic)
    (hb : ∀ s, interpolate K (fun v => repair (signedContrast (c v))) (boundary s) = (f s).val) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have := cone_realization_contractible K apex hapex hcone
  exact interpolated_approximate_edge K c ε δ μ hμ h0 h1 hp hm boundary f hnonnull hb

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
