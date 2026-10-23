import Foundation.Crypto.Semantics.Probability.ClassicalBitTetrahedralBoundary
import Foundation.ThirdParty.Brouwer.Brouwer

/-! Concrete zero-forcing for the tetrahedral boundary, using the previously
formalized Brouwer theorem (MIT, Math_XMUM). No boundary-nonnullity premise
occurs in `sharp_normalized_extension_forces_zero`. This does not itself
construct a nullhomotopy-to-extension bridge for the boundary map. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section

abbrev TetrahedralSimplex := ↥(stdSimplex ℝ (Fin 4))

def sharpAffine (x : TetrahedralSimplex) (i : Fin 4) : ℝ := 1 / 6 - (2 / 3) * x.val i

theorem positive_negative_of_zero_sum (w : Fin 4 → ℝ) (hb : bias w = 0) (hnz : w ≠ 0) :
    0 < positiveMass w ∧ 0 < negativeMass w := by
  have hm := mass_pos_of_ne_zero w hnz
  have hs := mass_parts w
  have hd := bias_parts w
  constructor <;> linarith

def positiveSimplex (w : Fin 4 → ℝ) (hp : 0 < positiveMass w) : TetrahedralSimplex :=
  ⟨fun i => max (w i) 0 / positiveMass w, by
    constructor
    · intro i
      exact div_nonneg (le_max_right _ _) (le_of_lt hp)
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hp)⟩

theorem negative_coordinate (w : Fin 4 → ℝ) (hn : 0 < negativeMass w) :
    ∃ i, w i < 0 := by
  by_contra h
  push Not at h
  have heq : negativeMass w = 0 := by
    unfold negativeMass
    simp_rw [max_eq_right (neg_nonpos.mpr (h _))]
    simp
  linarith

theorem sharpAffine_ne_zero_at_boundary (x : TetrahedralSimplex)
    (hx : ∃ i, x.val i = 0) : sharpAffine x ≠ 0 := by
  obtain ⟨i, hi⟩ := hx
  intro hz
  have h := congrFun hz i
  norm_num [sharpAffine, hi] at h

/-- Concrete boundary condition: normalize the affine tetrahedral labels.
No topological nonnullity assumption, custom axiom, or homology interface is
used; the fixed-point theorem supplies the global obstruction. -/
theorem sharp_normalized_extension_forces_zero (F : C(TetrahedralSimplex, Fin 4 → ℝ))
    (hb : ∀ x, bias (F x) = 0)
    (hboundary : ∀ x, (∃ i, x.val i = 0) →
      normalizeSigned (F x) = normalizeSigned (sharpAffine x)) :
    ∃ x, F x = 0 := by
  by_contra h
  push Not at h
  have hparts (x : TetrahedralSimplex) := positive_negative_of_zero_sum (F x) (hb x) (h x)
  let g : TetrahedralSimplex → TetrahedralSimplex := fun x => positiveSimplex (F x) (hparts x).1
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hnum : Continuous (fun x => max (F x i) 0) :=
      ((continuous_apply i).comp F.continuous).max continuous_const
    have hden : Continuous (fun x => positiveMass (F x)) :=
      continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp F.continuous).max continuous_const
    exact hnum.div hden (fun x => ne_of_gt (hparts x).1)
  obtain ⟨x, hfixed⟩ := Brouwer (n := (4 : ℕ+)) g hg
  have hfixed_coord (i : Fin 4) : max (F x i) 0 / positiveMass (F x) = x.val i :=
    congrFun (congrArg Subtype.val hfixed) i
  obtain ⟨k, hk⟩ := negative_coordinate (F x) (hparts x).2
  have hxk : x.val k = 0 := by
    have hcoord := hfixed_coord k
    rw [max_eq_right (le_of_lt hk), zero_div] at hcoord
    exact hcoord.symm
  have hnorm := hboundary x ⟨k, hxk⟩
  have hmF : 0 < mass (F x) := mass_pos_of_ne_zero (F x) (h x)
  have hmA : 0 < mass (sharpAffine x) :=
    mass_pos_of_ne_zero (sharpAffine x) (sharpAffine_ne_zero_at_boundary x ⟨k, hxk⟩)
  have hxsmall (i : Fin 4) : x.val i < 1 / 4 := by
    by_cases hxi : 0 < x.val i
    · have hmaxeq : max (F x i) 0 = x.val i * positiveMass (F x) :=
        (div_eq_iff (ne_of_gt (hparts x).1)).mp (hfixed_coord i)
      have hmaxpos : 0 < max (F x i) 0 := by
        rw [hmaxeq]
        exact mul_pos hxi (hparts x).1
      have hFpos : 0 < F x i := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmaxpos
      have hquot : 0 < sharpAffine x i / mass (sharpAffine x) := by
        rw [← show F x i / mass (F x) = sharpAffine x i / mass (sharpAffine x) from congrFun hnorm i]
        exact div_pos hFpos hmF
      have hApos : 0 < sharpAffine x i := by
        have hp := mul_pos hquot hmA
        simpa only [div_mul_cancel₀ _ (ne_of_gt hmA)] using hp
      dsimp [sharpAffine] at hApos
      linarith
    · have hle : x.val i ≤ 0 := le_of_not_gt hxi
      linarith
  have hsum := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    Finset.univ_nonempty (fun i _ => hxsmall i)
  norm_num at hsum
  have htotal : (∑ i : Fin 4, x.val i) = 1 := x.property.2
  rw [htotal] at hsum
  exact (lt_irrefl (1 : ℝ)) hsum

theorem sharpTetrahedron_entry (v k : Fin 4) :
    (sharpTetrahedron v).signed k = 1 / 6 - (if v = k then 2 / 3 else 0) := by
  by_cases hv : v = k
  · subst v
    norm_num [sharpTetrahedron]
  · have hk : k.val ≠ v.val := by
      intro h
      exact hv (Fin.ext h).symm
    change (if k.val = v.val then -1 / 2 else 1 / 6 : ℝ) = _
    rw [if_neg hk, if_neg hv]
    ring

/-- Identifies the boundary formula with the original four cipher labels. -/
theorem sharpAffine_eq_weighted_labels (x : TetrahedralSimplex) :
    sharpAffine x = ∑ v : Fin 4, x.val v • (sharpTetrahedron v).signed := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sharpTetrahedron_entry]
  simp_rw [mul_sub, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_ite_eq']
  have hsum : (∑ i : Fin 4, x.val i) = 1 := x.property.2
  simp only [hsum, one_mul, Finset.mem_univ, ↓reduceIte]
  dsimp [sharpAffine]
  ring

def sharpAffineMap : C(TetrahedralSimplex, Fin 4 → ℝ) where
  toFun := sharpAffine
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact continuous_const.sub (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val))

theorem sharpAffine_bias (x : TetrahedralSimplex) : bias (sharpAffine x) = 0 := by
  have htotal : (∑ i : Fin 4, x.val i) = 1 := x.property.2
  unfold bias sharpAffine
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htotal]
  norm_num

def tetrahedralCenter : TetrahedralSimplex :=
  ⟨fun _ => 1 / 4, by constructor; intro i; norm_num; norm_num⟩

theorem sharpAffine_center_zero : sharpAffine tetrahedralCenter = 0 := by
  funext i
  norm_num [sharpAffine, tetrahedralCenter]

theorem sharp_parameterized_perfect_edge {Vertex : Type*} [Fintype Vertex]
    (K : PreAbstractSimplicialComplex Vertex) (d : Vertex → PerfectCipher (Fin 4))
    (weights : C(TetrahedralSimplex, Realization K))
    (hboundary : ∀ x, (∃ i, x.val i = 0) →
      normalizeSigned (interpolate K (fun v => (d v).signed) (weights x)) =
        normalizeSigned (sharpAffine x)) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  let F := (interpolate K (fun v => (d v).signed)).comp weights
  obtain ⟨x, hx⟩ := sharp_normalized_extension_forces_zero F
    (fun x => interpolate_bias K _ (fun v => (d v).bias_zero) (weights x)) hboundary
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cover K (fun v => (d v).signed) (weights x)
  change interpolate K (fun v => (d v).signed) (weights x) = 0 at hx
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := perfect_cell_edge_jump d cell (faceEdge K) hcell hmem
  exact ⟨u, v, huv, hdist⟩

theorem sharp_parameterized_approximate_edge {Vertex : Type*} [Fintype Vertex]
    (K : PreAbstractSimplicialComplex Vertex) (c : Vertex → Cipher (Fin 4))
    (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (weights : C(TetrahedralSimplex, Realization K))
    (hboundary : ∀ x, (∃ i, x.val i = 0) →
      normalizeSigned (interpolate K (fun v => repair (signedContrast (c v))) (weights x)) =
        normalizeSigned (sharpAffine x)) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have hmargin (i : Vertex) := repair_margin_bound (c i) (ε i) (δ i) μ
    (h0 i) (h1 i) (hp i) (hm i)
  have hbias (i : Vertex) : bias (repair (signedContrast (c i))) = 0 := by
    apply repair_bias <;> linarith [(hmargin i).1, (hmargin i).2]
  let F := (interpolate K (fun v => repair (signedContrast (c v)))).comp weights
  obtain ⟨x, hx⟩ := sharp_normalized_extension_forces_zero F
    (fun x => interpolate_bias K _ hbias (weights x)) hboundary
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cover K (fun v => repair (signedContrast (c v))) (weights x)
  change interpolate K (fun v => repair (signedContrast (c v))) (weights x) = 0 at hx
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := approximate_cell_edge_jump c cell (faceEdge K) hcell
    ε δ μ hμ (fun i _ => h0 i) (fun i _ => h1 i)
    (fun i _ => hp i) (fun i _ => hm i) hmem
  exact ⟨u, v, huv, hdist⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
