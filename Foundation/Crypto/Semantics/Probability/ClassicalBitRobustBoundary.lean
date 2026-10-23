import Foundation.Crypto.Semantics.Probability.ClassicalBitBrouwerObstruction

/-! The concrete boundary obstruction tolerates coordinate errors up to 1/18.
This permits dyadic approximations; it does not certify a particular mesh or
its projective barycentric parameterization. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section

theorem sharpAffine_mass_le_one (x : TetrahedralSimplex) : mass (sharpAffine x) ≤ 1 := by
  have htotal : (∑ i : Fin 4, x.val i) = 1 := x.property.2
  have hcoord (i : Fin 4) : |sharpAffine x i| ≤ 1 / 6 + x.val i / 3 := by
    have hx0 := x.property.1 i
    have hx1 : x.val i ≤ 1 := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (fun j _ => x.property.1 j) (Finset.mem_univ i)
      rwa [htotal] at h
    apply abs_le.mpr
    dsimp [sharpAffine]
    constructor <;> linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hcoord i
  rw [Finset.sum_add_distrib] at hs
  simp_rw [← Finset.sum_div] at hs
  rw [htotal] at hs
  norm_num at hs
  exact hs

/-- A uniform error of 1/18 in each normalized boundary coordinate still forces
a zero. A fixed point has at least one zero coordinate, so only three positive
coordinates, each strictly below 1/3, must sum to one. -/
theorem robust_sharp_extension_forces_zero (F : C(TetrahedralSimplex, Fin 4 → ℝ))
    (hb : ∀ x, bias (F x) = 0)
    (hboundary : ∀ x, (∃ i, x.val i = 0) → ∀ i,
      |normalizeSigned (F x) i - normalizeSigned (sharpAffine x) i| ≤ 1 / 18) :
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
  have hmF : 0 < mass (F x) := mass_pos_of_ne_zero (F x) (h x)
  have hmA : 0 < mass (sharpAffine x) :=
    mass_pos_of_ne_zero (sharpAffine x) (sharpAffine_ne_zero_at_boundary x ⟨k, hxk⟩)
  have hmA1 := sharpAffine_mass_le_one x
  have hxsmall (i : Fin 4) : x.val i < 1 / 3 := by
    by_cases hxi : 0 < x.val i
    · have hmaxeq : max (F x i) 0 = x.val i * positiveMass (F x) :=
        (div_eq_iff (ne_of_gt (hparts x).1)).mp (hfixed_coord i)
      have hmaxpos : 0 < max (F x i) 0 := by rw [hmaxeq]; exact mul_pos hxi (hparts x).1
      have hFpos : 0 < F x i := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmaxpos
      have hFquot : 0 < normalizeSigned (F x) i := div_pos hFpos hmF
      have herror := (abs_le.mp (hboundary x ⟨k, hxk⟩ i)).2
      have hAquot : -(1 / 18 : ℝ) < sharpAffine x i / mass (sharpAffine x) := by
        change normalizeSigned (F x) i - sharpAffine x i / mass (sharpAffine x) ≤ _ at herror
        linarith
      have hmul := mul_lt_mul_of_pos_right hAquot hmA
      rw [div_mul_cancel₀ _ (ne_of_gt hmA)] at hmul
      have hA : -(1 / 18 : ℝ) < sharpAffine x i := by linarith
      dsimp [sharpAffine] at hA
      linarith
    · have hle : x.val i ≤ 0 := le_of_not_gt hxi
      linarith
  have hne : (Finset.univ.erase k : Finset (Fin 4)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
    norm_num
  have hsum := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hxsmall i)
  have htotal : (∑ i : Fin 4, x.val i) = 1 := x.property.2
  have herase : (∑ i ∈ (Finset.univ.erase k : Finset (Fin 4)), x.val i) = 1 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin 4 => x.val i)
      (Finset.mem_univ k)
    rw [htotal, hxk, add_zero] at hh
    exact hh
  rw [herase] at hsum
  norm_num [Finset.card_erase_of_mem (Finset.mem_univ k)] at hsum

theorem robust_sharp_parameterized_perfect_edge {Vertex : Type*} [Fintype Vertex]
    (K : PreAbstractSimplicialComplex Vertex) (d : Vertex → PerfectCipher (Fin 4))
    (weights : C(TetrahedralSimplex, Realization K))
    (hboundary : ∀ x, (∃ i, x.val i = 0) → ∀ i,
      |normalizeSigned (interpolate K (fun v => (d v).signed) (weights x)) i -
        normalizeSigned (sharpAffine x) i| ≤ 1 / 18) :
    ∃ u v, faceEdge K u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  let F := (interpolate K (fun v => (d v).signed)).comp weights
  obtain ⟨x, hx⟩ := robust_sharp_extension_forces_zero F
    (fun x => interpolate_bias K _ (fun v => (d v).bias_zero) (weights x)) hboundary
  obtain ⟨cell, hcell, hmem⟩ := interpolate_cover K (fun v => (d v).signed) (weights x)
  change interpolate K (fun v => (d v).signed) (weights x) = 0 at hx
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := perfect_cell_edge_jump d cell (faceEdge K) hcell hmem
  exact ⟨u, v, huv, hdist⟩

theorem robust_sharp_parameterized_approximate_edge {Vertex : Type*} [Fintype Vertex]
    (K : PreAbstractSimplicialComplex Vertex) (c : Vertex → Cipher (Fin 4))
    (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (weights : C(TetrahedralSimplex, Realization K))
    (hboundary : ∀ x, (∃ i, x.val i = 0) → ∀ i,
      |normalizeSigned (interpolate K (fun v => repair (signedContrast (c v))) (weights x)) i -
        normalizeSigned (sharpAffine x) i| ≤ 1 / 18) :
    ∃ u v, faceEdge K u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have hmargin (i : Vertex) := repair_margin_bound (c i) (ε i) (δ i) μ
    (h0 i) (h1 i) (hp i) (hm i)
  have hbias (i : Vertex) : bias (repair (signedContrast (c i))) = 0 := by
    apply repair_bias <;> linarith [(hmargin i).1, (hmargin i).2]
  let F := (interpolate K (fun v => repair (signedContrast (c v)))).comp weights
  obtain ⟨x, hx⟩ := robust_sharp_extension_forces_zero F
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
