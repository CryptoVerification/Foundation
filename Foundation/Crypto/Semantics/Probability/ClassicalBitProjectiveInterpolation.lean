import Foundation.Crypto.Semantics.Probability.ClassicalBitBoundaryError

/-! Global finite barycentric data determine the boundary estimate.
Inactive vertices need not lie on the boundary or carry rounding certificates. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
variable {Vertex : Type*} [Fintype Vertex]

def projectiveScale (p : TetrahedralSimplex) : ℝ := max (mass (sharpAffine p)) (1 / 3)

def projectiveDenominator (a : Vertex → ℝ) (p : Vertex → TetrahedralSimplex) : ℝ :=
  ∑ i, a i * projectiveScale (p i)

def projectiveMixture (a : Vertex → ℝ) (p : Vertex → TetrahedralSimplex)
    (q : Vertex → Fin 4 → ℝ) : Fin 4 → ℝ :=
  ∑ i, (a i * projectiveScale (p i) / projectiveDenominator a p) • q i

/-- A zero coordinate of a barycenter forces every active vertex onto the same face. -/
theorem active_vertex_on_boundary (a : Vertex → ℝ) (p : Vertex → TetrahedralSimplex)
    (x : TetrahedralSimplex) (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ k, ∑ i, a i * (p i).val k = x.val k)
    (hb : ∃ k, x.val k = 0) (i : Vertex) (hi : a i ≠ 0) :
    ∃ k, (p i).val k = 0 := by
  obtain ⟨k, hk⟩ := hb
  have hn (j : Vertex) : 0 ≤ a j * (p j).val k := mul_nonneg (ha j) ((p j).property.1 k)
  have hle := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
  rw [hx k, hk] at hle
  exact ⟨k, (mul_eq_zero.mp (le_antisymm hle (hn i))).resolve_left hi⟩

/-- The global list may contain interior vertices. Boundary support and the
normalization error are consequences of barycentric reconstruction. -/
theorem projectiveMixture_boundary_error (a : Vertex → ℝ)
    (p : Vertex → TetrahedralSimplex) (q : Vertex → Fin 4 → ℝ)
    (x : TetrahedralSimplex) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hx : ∀ k, ∑ i, a i * (p i).val k = x.val k) (hb : ∃ k, x.val k = 0)
    (hq : ∀ i, bias (q i) = 0)
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (q i) (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64)
    (k : Fin 4) :
    |normalizeSigned (projectiveMixture a p q) k -
      normalizeSigned (sharpAffine x) k| ≤ 3 / 64 := by
  classical
  let b : TetrahedralSimplex := ⟨fun j => if j = 0 then 1 else 0, by
    constructor
    · intro j; dsimp; split_ifs <;> norm_num
    · simp⟩
  have hb0 : ∃ k, b.val k = 0 := ⟨1, by norm_num [b]⟩
  let p' := fun i => if a i = 0 then b else p i
  let q' := fun i => if a i = 0 then normalizeSigned (sharpAffine b) else q i
  have hp' (i : Vertex) : ∃ j, (p' i).val j = 0 := by
    dsimp [p']; split_ifs with hi
    · exact hb0
    · exact active_vertex_on_boundary a p x ha hx hb i hi
  have hq' (i : Vertex) : bias (q' i) = 0 := by
    dsimp [q']; split_ifs
    · exact normalizeSigned_bias _ (sharpAffine_bias b)
    · exact hq i
  have he' (i : Vertex) : l1Distance (q' i) (normalizeSigned (sharpAffine (p' i))) ≤ 1 / 64 := by
    dsimp [q', p']; split_ifs with hi
    · simp [l1Distance]
    · exact he i (active_vertex_on_boundary a p x ha hx hb i hi)
  have hx' (j : Fin 4) : ∑ i, a i * (p' i).val j = x.val j := by
    rw [← hx j]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i = 0 <;> simp [p', hi]
  have hscale (i : Vertex) : a i * projectiveScale (p i) = a i * mass (sharpAffine (p' i)) := by
    by_cases hi : a i = 0
    · simp [hi]
    · have hbound := sharpAffine_boundary_mass_lower (p i)
        (active_vertex_on_boundary a p x ha hx hb i hi)
      dsimp [projectiveScale]
      rw [max_eq_left hbound]
      simp only [p', if_neg hi]
  have hden : projectiveDenominator a p = boundaryScaleSum a p' := by
    unfold projectiveDenominator boundaryScaleSum
    exact Finset.sum_congr rfl (fun i _ => hscale i)
  have hmix : projectiveMixture a p q = ∑ i, boundaryCoefficient a p' i • q' i := by
    unfold projectiveMixture boundaryCoefficient
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i = 0
    · simp [hi]
    · rw [hscale, hden]
      simp [q', hi]
  rw [hmix]
  exact projective_eight_bit_boundary_error a p' q' x ha hs hp' hb hx' hq' he' k

theorem projectiveDenominator_lower (a : Vertex → ℝ) (p : Vertex → TetrahedralSimplex)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) :
    1 / 3 ≤ projectiveDenominator a p := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (le_max_right (mass (sharpAffine (p i))) (1 / 3)) (ha i)
  rw [← Finset.sum_mul, hs, one_mul] at h
  exact h

/-- Continuous barycentric weights produce a continuous projective interpolant;
positivity of its denominator follows from normalization of the weights. -/
def projectiveInterpolation (a : Vertex → C(TetrahedralSimplex, ℝ))
    (p : Vertex → TetrahedralSimplex) (q : Vertex → Fin 4 → ℝ)
    (ha : ∀ x i, 0 ≤ a i x) (hs : ∀ x, ∑ i, a i x = 1) :
    C(TetrahedralSimplex, Fin 4 → ℝ) where
  toFun x := projectiveMixture (fun i => a i x) p q
  continuous_toFun := by
    have hd : Continuous (fun x => projectiveDenominator (fun i => a i x) p) :=
      continuous_finsetSum _ fun i _ => (a i).continuous.mul continuous_const
    have hn (x : TetrahedralSimplex) : projectiveDenominator (fun i => a i x) p ≠ 0 := by
      have h := projectiveDenominator_lower (fun i => a i x) p (ha x) (hs x)
      linarith
    apply continuous_pi
    intro k
    simp only [projectiveMixture, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ =>
      (((a i).continuous.mul continuous_const).div hd hn).mul continuous_const

/-- Only finite vertex certificates, continuous normalized weights, and their
barycentric reconstruction are supplied. No pointwise boundary witness or
global boundary error estimate is an input. -/
theorem projectiveInterpolation_forces_zero (a : Vertex → C(TetrahedralSimplex, ℝ))
    (p : Vertex → TetrahedralSimplex) (q : Vertex → Fin 4 → ℝ)
    (ha : ∀ x i, 0 ≤ a i x) (hs : ∀ x, ∑ i, a i x = 1)
    (hx : ∀ x k, ∑ i, a i x * (p i).val k = x.val k)
    (hq : ∀ i, bias (q i) = 0)
    (he : ∀ i, (∃ k, (p i).val k = 0) →
      l1Distance (q i) (normalizeSigned (sharpAffine (p i))) ≤ 1 / 64) :
    ∃ x, projectiveInterpolation a p q ha hs x = 0 := by
  apply robust_sharp_extension_forces_zero
  · intro x
    exact weighted_bias_zero _ q hq
  · intro x hb k
    exact le_trans (projectiveMixture_boundary_error (fun i => a i x) p q x
      (ha x) (hs x) (hx x) hb hq he k) (by norm_num)

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
