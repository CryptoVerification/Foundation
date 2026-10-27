import Foundation.Crypto.Semantics.Probability.ClassicalBitMeshCoordinates

/-! Local geometric conditions imply the global coordinate homeomorphism.
No continuous inverse, global matching map, or bijectivity proof is supplied. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
variable {Vertex : Type*} [Fintype Vertex]

/-- Replace a global sum by its restriction to a known finite support. -/
theorem sum_supported_on_face {M : Type*} [AddCommMonoid M]
    (cell : Finset Vertex) (f : Vertex → M) (hf : ∀ i, i ∉ cell → f i = 0) :
    (∑ i, f i) = ∑ i : cell, f i := by
  classical
  rw [Finset.univ_eq_attach, Finset.sum_attach]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i hi)).symm

/-- A point in a finite geometric face has nonnegative normalized weights,
extended by zero to all other vertices. Distinct vertex labels are retained. -/
theorem face_weights_of_mem_convexHull (r : Vertex → Fin 4 → ℝ)
    (hr : Function.Injective r) (cell : Finset Vertex) (x : Fin 4 → ℝ)
    (hx : x ∈ convexHull ℝ (r '' (cell : Set Vertex))) :
    ∃ a : Vertex → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧
      (∀ i, i ∉ cell → a i = 0) ∧ (∑ i, a i • r i) = x := by
  classical
  have hx' : x ∈ convexHull ℝ (↑(cell.image r) : Set (Fin 4 → ℝ)) := by
    simpa only [Finset.coe_image] using hx
  obtain ⟨w, hw, hs, he⟩ := Finset.mem_convexHull'.mp hx'
  rw [Finset.sum_image (fun i _ j _ h => hr h)] at hs he
  let a := fun i => if i ∈ cell then w (r i) else 0
  have hsum : (∑ i, a i) = ∑ i ∈ cell, w (r i) := by
    simp [a]
  have hvec : (∑ i, a i • r i) = ∑ i ∈ cell, w (r i) • r i := by
    simp [a, ite_smul]
  refine ⟨a, ?_, hsum.trans hs, ?_, hvec.trans he⟩
  · intro i
    dsimp [a]
    split_ifs with hi
    · exact hw _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact le_refl _
  · intro i hi
    simp [a, hi]

theorem supported_weights_mem_convexHull (r : Vertex → Fin 4 → ℝ)
    (cell : Finset Vertex) (a : Vertex → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : ∑ i, a i = 1) (ht : ∀ i, i ∉ cell → a i = 0) :
    (∑ i, a i • r i) ∈ convexHull ℝ (r '' (cell : Set Vertex)) := by
  have hsum := sum_supported_on_face cell a ht
  have hvec := sum_supported_on_face cell (fun i => a i • r i)
    (fun i hi => by rw [ht i hi, zero_smul])
  exact mem_convexHull_of_exists_fintype (s := r '' (cell : Set Vertex)) (fun i : cell => a i) (fun i : cell => r i)
    (fun i => ha i) (hsum.symm.trans hs) (fun i => ⟨i, i.property, rfl⟩) hvec.symm

/-- Affine independence is needed only inside the given face. -/
theorem face_weights_unique (r : Vertex → Fin 4 → ℝ) (cell : Finset Vertex)
    (hind : AffineIndependent ℝ (fun i : cell => r i)) (a b : Vertex → ℝ)
    (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1)
    (hta : ∀ i, i ∉ cell → a i = 0) (htb : ∀ i, i ∉ cell → b i = 0)
    (he : (∑ i, a i • r i) = ∑ i, b i • r i) : a = b := by
  classical
  have hsa := sum_supported_on_face cell a hta
  have hsb := sum_supported_on_face cell b htb
  have hva := sum_supported_on_face cell (fun i => a i • r i)
    (fun i hi => by rw [hta i hi, zero_smul])
  have hvb := sum_supported_on_face cell (fun i => b i • r i)
    (fun i hi => by rw [htb i hi, zero_smul])
  have hsum : (∑ i : cell, a i) = ∑ i : cell, b i := by rw [← hsa, ← hsb, ha, hb]
  have hvec : (∑ i : cell, a i • r i) = ∑ i : cell, b i • r i := by
    rw [← hva, ← hvb]; exact he
  have hu := hind.eq_of_sum_eq_sum (s := Finset.univ) hsum hvec
  funext i
  by_cases hi : i ∈ cell
  · exact hu ⟨i, hi⟩ (Finset.mem_univ _)
  · rw [hta i hi, htb i hi]

/-- These are geometric cover and face-gluing obligations, not assumptions
about a global correspondence of cryptographic proof executions. -/
structure MeshGeometry (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) : Prop where
  distinct : Function.Injective (fun i => (p i).val)
  independent : ∀ cell ∈ K, AffineIndependent ℝ (fun i : cell => (p i).val)
  common_face : ∀ s ∈ K, ∀ t ∈ K,
    convexHull ℝ ((fun i => (p i).val) '' (s : Set Vertex)) ∩
      convexHull ℝ ((fun i => (p i).val) '' (t : Set Vertex)) ⊆
      convexHull ℝ ((fun i => (p i).val) '' ((s : Set Vertex) ∩ (t : Set Vertex)))
  cover : ∀ x : TetrahedralSimplex, ∃ cell ∈ K,
    x.val ∈ convexHull ℝ ((fun i => (p i).val) '' (cell : Set Vertex))

theorem meshGeometry_projection_injective (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (g : MeshGeometry K p) :
    Function.Injective (meshProjection K p) := by
  classical
  intro w v he
  let r := fun i => (p i).val
  obtain ⟨s, hs, hws⟩ := w.property.2.2
  obtain ⟨t, ht, hvt⟩ := v.property.2.2
  have hwout (i : Vertex) (hi : i ∉ s) : w.val i = 0 := by
    by_contra hn; exact hi (hws i hn)
  have hvout (i : Vertex) (hi : i ∉ t) : v.val i = 0 := by
    by_contra hn; exact hi (hvt i hn)
  have hsame : (∑ i, w.val i • r i) = ∑ i, v.val i • r i := by
    have hh := congrArg Subtype.val he
    funext k
    have hh' : (∑ i, w.val i * (p i).val k) = (∑ i, v.val i * (p i).val k) := congrFun hh k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh'
  have hw := supported_weights_mem_convexHull r s w.val w.property.1 w.property.2.1 hwout
  have hv := supported_weights_mem_convexHull r t v.val v.property.1 v.property.2.1 hvout
  rw [← hsame] at hv
  have hc := g.common_face s hs t ht ⟨hw, hv⟩
  have hc' : (∑ i, w.val i • r i) ∈ convexHull ℝ (r '' (↑(s ∩ t) : Set Vertex)) := by
    simpa only [Finset.coe_inter] using hc
  obtain ⟨a, _, ha, hat, heq⟩ := face_weights_of_mem_convexHull r g.distinct (s ∩ t) _ hc'
  have has (i : Vertex) (hi : i ∉ s) : a i = 0 :=
    hat i (fun h => hi (Finset.mem_inter.mp h).1)
  have hat' (i : Vertex) (hi : i ∉ t) : a i = 0 :=
    hat i (fun h => hi (Finset.mem_inter.mp h).2)
  have hwa := face_weights_unique r s (g.independent s hs) w.val a
    w.property.2.1 ha hwout has heq.symm
  have hva := face_weights_unique r t (g.independent t ht) v.val a
    v.property.2.1 ha hvout hat' (hsame.symm.trans heq.symm)
  exact Subtype.ext (hwa.trans hva.symm)

theorem meshGeometry_projection_surjective (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (g : MeshGeometry K p) :
    Function.Surjective (meshProjection K p) := by
  intro x
  obtain ⟨cell, hc, hx⟩ := g.cover x
  obtain ⟨a, ha, hs, ht, he⟩ := face_weights_of_mem_convexHull _ g.distinct cell x.val hx
  let w : Realization K := ⟨a, ha, hs, cell, hc, fun i hi => by
    by_contra hn; exact hi (ht i hn)⟩
  refine ⟨w, Subtype.ext ?_⟩
  funext k
  change (∑ i, a i * (p i).val k) = x.val k
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun he k

theorem meshGeometry_projection_bijective (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (g : MeshGeometry K p) :
    Function.Bijective (meshProjection K p) :=
  ⟨meshGeometry_projection_injective K p g, meshGeometry_projection_surjective K p g⟩

/-- Local geometric conditions and finite boundary certificates suffice for
an edge obstruction. Global matching and continuous weights are constructed. -/
theorem geometric_mesh_perfect_edge (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (g : MeshGeometry K p)
    (d : Vertex → PerfectCipher (Fin 4))
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (d i).signed (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message :=
  mesh_projective_perfect_edge K p (meshGeometry_projection_bijective K p g) d he

theorem geometric_mesh_approximate_edge (K : PreAbstractSimplicialComplex Vertex)
    (p : Vertex → TetrahedralSimplex) (g : MeshGeometry K p)
    (c : Vertex → Cipher (Fin 4)) (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (repair (signedContrast (c i)))
        (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) :=
  mesh_projective_approximate_edge K p (meshGeometry_projection_bijective K p g)
    c ε δ μ hμ h0 h1 hp hm he

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
