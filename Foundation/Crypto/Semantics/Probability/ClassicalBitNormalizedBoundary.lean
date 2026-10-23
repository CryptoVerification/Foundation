import Foundation.Crypto.Semantics.Probability.ClassicalBitSimplicialInterpolation

/-! Normalized boundary conditions and canonical subcomplex inclusions.
Boundary mixtures may have l1 mass below one; only avoiding zero is required.
Non-nullity of the computed normalized boundary remains an explicit premise. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Key Vertex : Type*} [Fintype Key]

def perfectNormalization {X : Type*} [TopologicalSpace X] (F : C(X, Key → ℝ))
    (hbias : ∀ x, bias (F x) = 0) (hnz : ∀ x, F x ≠ 0) : C(X, PerfectVector Key) := by
  have hm (x : X) : 0 < mass (F x) := mass_pos_of_ne_zero (F x) (hnz x)
  have hc : Continuous (fun x => mass (F x)) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp F.continuous).abs
  have hnorm : Continuous (fun x => normalizeSigned (F x)) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp F.continuous).div hc (fun x => ne_of_gt (hm x))
  exact ⟨fun x => ⟨normalizeSigned (F x), normalizeSigned_bias _ (hbias x),
    normalizeSigned_mass _ (hnz x)⟩, hnorm.subtype_mk _⟩

theorem normalized_boundary_forces_zero {X Boundary : Type*}
    [TopologicalSpace X] [ContractibleSpace X] [TopologicalSpace Boundary]
    (boundary : C(Boundary, X)) (f : C(Boundary, PerfectVector Key))
    (hnonnull : ¬f.Nullhomotopic) (F : C(X, Key → ℝ))
    (hzero : ∀ x, bias (F x) = 0)
    (hboundary : ∀ s, normalizeSigned (F (boundary s)) = (f s).val) :
    ∃ x, F x = 0 := by
  by_contra h
  push Not at h
  let g := perfectNormalization F hzero h
  have heq : g.comp boundary = f := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact hboundary s
  have hnull : g.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic X).comp_right g
  apply hnonnull
  rw [← heq]
  exact hnull.comp_left boundary

section FiniteVertices
variable [Fintype Vertex]

def realizationInclusion (L K : PreAbstractSimplicialComplex Vertex) (hLK : L ≤ K) :
    C(Realization L, Realization K) := by
  have hmem (x : Realization L) : x.val ∈ realizationSet K := by
    refine ⟨x.property.1, x.property.2.1, ?_⟩
    obtain ⟨cell, hcell, hsupport⟩ := x.property.2.2
    exact ⟨cell, hLK hcell, hsupport⟩
  exact ⟨fun x => ⟨x.val, hmem x⟩, continuous_subtype_val.subtype_mk hmem⟩

omit [Fintype Key] in
theorem interpolate_inclusion (L K : PreAbstractSimplicialComplex Vertex) (hLK : L ≤ K)
    (label : Vertex → Key → ℝ) (x : Realization L) :
    interpolate K label (realizationInclusion L K hLK x) = interpolate L label x := rfl

omit [Fintype Key] in
theorem interpolate_ne_zero_of_face_hulls (L : PreAbstractSimplicialComplex Vertex)
    (label : Vertex → Key → ℝ)
    (havoid : ∀ cell ∈ L, (0 : Key → ℝ) ∉ convexHull ℝ (label '' (cell : Set Vertex)))
    (x : Realization L) : interpolate L label x ≠ 0 := by
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cell L label x
  intro hz
  rw [hz] at hmem
  exact havoid cell hcell hmem

def normalizedBoundary (L : PreAbstractSimplicialComplex Vertex)
    (d : Vertex → PerfectCipher Key)
    (havoid : ∀ cell ∈ L, (0 : Key → ℝ) ∉
      convexHull ℝ ((fun i => (d i).signed) '' (cell : Set Vertex))) :
    C(Realization L, PerfectVector Key) :=
  perfectNormalization (interpolate L (fun i => (d i).signed))
    (interpolate_bias L _ (fun i => (d i).bias_zero))
    (interpolate_ne_zero_of_face_hulls L _ havoid)

theorem normalized_subcomplex_forces_zero (L K : PreAbstractSimplicialComplex Vertex)
    (hLK : L ≤ K) [ContractibleSpace (Realization K)] (d : Vertex → PerfectCipher Key)
    (havoid : ∀ cell ∈ L, (0 : Key → ℝ) ∉
      convexHull ℝ ((fun i => (d i).signed) '' (cell : Set Vertex)))
    (hnonnull : ¬(normalizedBoundary L d havoid).Nullhomotopic) :
    ∃ x, interpolate K (fun i => (d i).signed) x = 0 := by
  exact normalized_boundary_forces_zero (realizationInclusion L K hLK)
    (normalizedBoundary L d havoid) hnonnull (interpolate K (fun i => (d i).signed))
    (interpolate_bias K _ (fun i => (d i).bias_zero)) (fun _ => rfl)

theorem normalized_subcomplex_perfect_edge (L K : PreAbstractSimplicialComplex Vertex)
    (hLK : L ≤ K) [ContractibleSpace (Realization K)] (d : Vertex → PerfectCipher (Fin 4))
    (havoid : ∀ cell ∈ L, (0 : Fin 4 → ℝ) ∉
      convexHull ℝ ((fun i => (d i).signed) '' (cell : Set Vertex)))
    (hnonnull : ¬(normalizedBoundary L d havoid).Nullhomotopic) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨x, hx⟩ := normalized_subcomplex_forces_zero L K hLK d havoid hnonnull
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cover K (fun i => (d i).signed) x
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := perfect_cell_edge_jump d cell (faceEdge K) hcell hmem
  exact ⟨u, v, huv, hdist⟩

def repairedFamily (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ)
    (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ) (i : Vertex) : PerfectCipher (Fin 4) :=
  repairedCipher (c i) (ε i) (δ i) (h0 i) (h1 i) (hp i) (by linarith [hm i])

theorem normalized_subcomplex_approximate_edge (L K : PreAbstractSimplicialComplex Vertex)
    (hLK : L ≤ K) [ContractibleSpace (Realization K)]
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (havoid : ∀ cell ∈ L, (0 : Fin 4 → ℝ) ∉ convexHull ℝ
      ((fun i => (repairedFamily c ε δ μ hμ h0 h1 hp hm i).signed) '' (cell : Set Vertex)))
    (hnonnull : ¬(normalizedBoundary L (repairedFamily c ε δ μ hμ h0 h1 hp hm) havoid).Nullhomotopic) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  obtain ⟨x, hx⟩ := normalized_subcomplex_forces_zero L K hLK
    (repairedFamily c ε δ μ hμ h0 h1 hp hm) havoid hnonnull
  have hx' : interpolate K (fun i => repair (signedContrast (c i))) x = 0 := hx
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cover K (fun i => repair (signedContrast (c i))) x
  rw [hx'] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := approximate_cell_edge_jump c cell (faceEdge K) hcell
    ε δ μ hμ (fun i _ => h0 i) (fun i _ => h1 i)
    (fun i _ => hp i) (fun i _ => hm i) hmem
  exact ⟨u, v, huv, hdist⟩

theorem normalized_cone_perfect_edge [DecidableEq Vertex]
    (L K : PreAbstractSimplicialComplex Vertex) (hLK : L ≤ K)
    (apex : Vertex) (hapex : {apex} ∈ K) (hcone : ∀ cell ∈ K, insert apex cell ∈ K)
    (d : Vertex → PerfectCipher (Fin 4))
    (havoid : ∀ cell ∈ L, (0 : Fin 4 → ℝ) ∉
      convexHull ℝ ((fun i => (d i).signed) '' (cell : Set Vertex)))
    (hnonnull : ¬(normalizedBoundary L d havoid).Nullhomotopic) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  have := cone_realization_contractible K apex hapex hcone
  exact normalized_subcomplex_perfect_edge L K hLK d havoid hnonnull

theorem normalized_cone_approximate_edge [DecidableEq Vertex]
    (L K : PreAbstractSimplicialComplex Vertex) (hLK : L ≤ K)
    (apex : Vertex) (hapex : {apex} ∈ K) (hcone : ∀ cell ∈ K, insert apex cell ∈ K)
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (havoid : ∀ cell ∈ L, (0 : Fin 4 → ℝ) ∉ convexHull ℝ
      ((fun i => (repairedFamily c ε δ μ hμ h0 h1 hp hm i).signed) '' (cell : Set Vertex)))
    (hnonnull : ¬(normalizedBoundary L (repairedFamily c ε δ μ hμ h0 h1 hp hm) havoid).Nullhomotopic) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have := cone_realization_contractible K apex hapex hcone
  exact normalized_subcomplex_approximate_edge L K hLK c ε δ μ hμ h0 h1 hp hm havoid hnonnull

end FiniteVertices
end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
