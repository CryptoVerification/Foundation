import Foundation.Crypto.Semantics.Probability.ClassicalBitSimplexCertificate

/-! Extract at most four signed ciphers from a zero-containing convex hull.
The input zero-in-convex-hull condition is not a boundary nonextension proof.
Existence uses mathlib's Carathéodory theorem, not an executable search. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section

def firstThree : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v i := v i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restoreFourth : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v k := if h : k.val < 3 then v ⟨k.val, h⟩ else -∑ i, v i
  map_add' v w := by
    funext k
    by_cases h : k.val < 3
    · simp [h]
    · simp [h, Finset.sum_add_distrib]
      ring
  map_smul' a v := by
    funext k
    by_cases h : k.val < 3 <;> simp [h, Finset.mul_sum]

theorem restore_firstThree (v : Fin 4 → ℝ) (hz : bias v = 0) :
    restoreFourth (firstThree v) = v := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have hs : (∑ i : Fin 3, v i.castSucc) + v (Fin.last 3) = 0 := by
      simpa only [bias, Fin.sum_univ_castSucc] using hz
    change (if h : (Fin.last 3).val < 3 then
      firstThree v ⟨(Fin.last 3).val, h⟩ else -∑ i, firstThree v i) = _
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    change -(∑ i : Fin 3, v i.castSucc) = v (Fin.last 3)
    linarith
  · change (if h : i.castSucc.val < 3 then
      firstThree v ⟨i.castSucc.val, h⟩ else -∑ j, firstThree v j) = _
    simp [i.isLt, firstThree]

theorem zero_convex_hull_three_small (s : Set (Fin 3 → ℝ))
    (hz : (0 : Fin 3 → ℝ) ∈ convexHull ℝ s) :
    ∃ t : Finset (Fin 3 → ℝ), (↑t : Set (Fin 3 → ℝ)) ⊆ s ∧
      t.card ≤ 4 ∧ (0 : Fin 3 → ℝ) ∈ convexHull ℝ (↑t : Set (Fin 3 → ℝ)) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hz
  have hi := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hz
  have hcard : t.card ≤ 4 := by
    calc
      t.card = Fintype.card t := by simp
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → (Fin 3 → ℝ)))) + 1 :=
        hi.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin 3 → ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = 4 := by simp
  exact ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hz, hcard,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hz⟩

/-- Zero-sum four-coordinate vectors live in three dimensions. The selected
finset contains original vectors, rather than newly invented convex mixtures. -/
theorem zero_convex_hull_small (s : Set (Fin 4 → ℝ))
    (hzero : ∀ v ∈ s, bias v = 0) (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ s) :
    ∃ t : Finset (Fin 4 → ℝ), (↑t : Set (Fin 4 → ℝ)) ⊆ s ∧
      t.card ≤ 4 ∧ (0 : Fin 4 → ℝ) ∈ convexHull ℝ (↑t : Set (Fin 4 → ℝ)) := by
  classical
  have hz3 : (0 : Fin 3 → ℝ) ∈ convexHull ℝ (firstThree '' s) := by
    rw [← firstThree.image_convexHull]
    exact ⟨0, hz, map_zero firstThree⟩
  obtain ⟨u, hus, hcard, hzu⟩ := zero_convex_hull_three_small (firstThree '' s) hz3
  let t := u.image restoreFourth
  have hts : (↑t : Set (Fin 4 → ℝ)) ⊆ s := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hzs, heq⟩ := hus hy
    rw [← heq, restore_firstThree z (hzero z hzs)]
    exact hzs
  refine ⟨t, hts, le_trans (Finset.card_image_le) hcard, ?_⟩
  have hzt : (0 : Fin 4 → ℝ) ∈ restoreFourth '' convexHull ℝ (↑u : Set (Fin 3 → ℝ)) :=
    ⟨0, hzu, map_zero restoreFourth⟩
  rwa [restoreFourth.image_convexHull, ← Finset.coe_image] at hzt

theorem small_weights_large {Point : Type*} [Fintype Point] [Nonempty Point]
    (α : Point → ℝ) (hc : Fintype.card Point ≤ 4) (hs : ∑ i, α i = 1) :
    ∃ i, 1 / 4 ≤ α i := by
  classical
  by_contra h
  push Not at h
  have ht := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    Finset.univ_nonempty (fun i _ => h i)
  have hr : (Fintype.card Point : ℝ) ≤ 4 := by exact_mod_cast hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs] at ht
  nlinarith

/-- A version of the local jump theorem for a nonempty type of at most four
vertices, so that padding a Carathéodory witness is unnecessary. -/
theorem small_unit_barycenter_pair {Point Key : Type*} [Fintype Point] [Nonempty Point]
    [Fintype Key] (v : Point → Key → ℝ) (α : Point → ℝ)
    (hc : Fintype.card Point ≤ 4) (ha : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hu : ∀ i, mass (v i) = 1) (hz : ∀ k, ∑ i, α i * v i k = 0) :
    ∃ i j, 4 / 3 ≤ l1Distance (v i) (v j) := by
  classical
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Point × Point => l1Distance (v p.1) (v p.2)) Finset.univ_nonempty
  let D := l1Distance (v p.1) (v p.2)
  have hD (i j : Point) : l1Distance (v i) (v j) ≤ D := hmax (i, j) (Finset.mem_univ _)
  obtain ⟨i, hi⟩ := small_weights_large α hc hs
  have hnonneg : 0 ≤ D := by simpa [l1Distance] using hD i i
  have hpoint (k : Key) : |v i k| ≤ ∑ j, α j * |v i k - v j k| := by
    have heq : (∑ j, α j * (v i k - v j k)) = v i k := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, hz]
      ring
    calc
      _ = |∑ j, α j * (v i k - v j k)| := congrArg abs heq.symm
      _ ≤ ∑ j, |α j * (v i k - v j k)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (ha _)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun k _ => hpoint k
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  change mass (v i) ≤ ∑ j, α j * l1Distance (v i) (v j) at hsum
  rw [hu] at hsum
  have hterm (j : Point) : α j * l1Distance (v i) (v j) ≤
      α j * D - (if j = i then α j * D else 0) := by
    by_cases hj : j = i
    · subst j
      simp [l1Distance]
    · simp only [hj, ↓reduceIte, sub_zero]
      exact mul_le_mul_of_nonneg_left (hD i j) (ha j)
  have hbound := Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs] at hbound
  simp only [one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hbound
  refine ⟨p.1, p.2, ?_⟩
  change 4 / 3 ≤ D
  nlinarith [mul_le_mul_of_nonneg_right hi hnonneg]

/-- The user need not select the four witnesses or their convex coefficients. -/
theorem zero_convex_hull_jump (s : Set (Fin 4 → ℝ))
    (hzero : ∀ v ∈ s, bias v = 0) (hunit : ∀ v ∈ s, mass v = 1)
    (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ s) :
    ∃ v ∈ s, ∃ w ∈ s, 4 / 3 ≤ l1Distance v w := by
  classical
  obtain ⟨t, hts, hcard, hzt⟩ := zero_convex_hull_small s hzero hz
  have htne : t.Nonempty := by
    rw [← Finset.coe_nonempty, ← @convexHull_nonempty_iff ℝ]
    exact ⟨0, hzt⟩
  have : Nonempty t := by
    obtain ⟨v, hv⟩ := htne
    exact ⟨⟨v, hv⟩⟩
  rw [t.convexHull_eq] at hzt
  obtain ⟨α, ha, hs, hc⟩ := hzt
  rw [t.centerMass_eq_of_sum_1 id hs] at hc
  have has : (∑ i : t, α i) = 1 := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hs
  have hcs : (∑ i : t, α i • (i : Fin 4 → ℝ)) = 0 := by
    rw [Finset.univ_eq_attach]
    change (∑ i ∈ t.attach, (fun v : Fin 4 → ℝ => α v • v) i) = 0
    rw [Finset.sum_attach (f := fun v : Fin 4 → ℝ => α v • v)]
    exact hc
  have hcoords (k : Fin 4) : (∑ i : t, α i * (i : Fin 4 → ℝ) k) = 0 := by
    have h := congrFun hcs k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  obtain ⟨v, w, hvw⟩ := small_unit_barycenter_pair (fun i : t => (i : Fin 4 → ℝ))
    (fun i : t => α i) (by simpa using hcard) (fun i => ha i i.property) has
    (fun i => hunit i (hts i.property)) hcoords
  exact ⟨v, hts v.property, w, hts w.property, hvw⟩

theorem perfect_convex_hull_jump {Index : Type*} (d : Index → PerfectCipher (Fin 4))
    (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ (Set.range (fun i => (d i).signed))) :
    ∃ i j, ∀ message, 2 / 3 ≤ jointTV (d i).toCipher (d j).toCipher message := by
  obtain ⟨v, ⟨i, rfl⟩, w, ⟨j, rfl⟩, hij⟩ := zero_convex_hull_jump
    (Set.range (fun i => (d i).signed))
    (by rintro _ ⟨i, rfl⟩; exact (d i).bias_zero)
    (by rintro _ ⟨i, rfl⟩; exact (d i).mass_one) hz
  refine ⟨i, j, fun message => ?_⟩
  rw [perfect_jointTV]
  linarith

/-- No four-point certificate or barycentric coefficients are user premises.
The remaining global premise is zero membership in the repaired convex hull. -/
theorem approximate_convex_hull_jump {Index : Type*} (c : Index → Cipher (Fin 4))
    (ε δ : Index → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ
      (Set.range (fun i => repair (signedContrast (c i))))) :
    ∃ i j, μ / 3 ≤ implementationDistance (c i) (c j) := by
  have hmargin (i : Index) := repair_margin_bound (c i) (ε i) (δ i) μ
    (h0 i) (h1 i) (hp i) (hm i)
  have hpos (i : Index) : 0 < positiveMass (signedContrast (c i)) := by
    linarith [(hmargin i).1]
  have hneg (i : Index) : 0 < negativeMass (signedContrast (c i)) := by
    linarith [(hmargin i).2]
  obtain ⟨v, ⟨i, rfl⟩, w, ⟨j, rfl⟩, hij⟩ := zero_convex_hull_jump
    (Set.range (fun i => repair (signedContrast (c i))))
    (by rintro _ ⟨i, rfl⟩; exact repair_bias _ (hpos i) (hneg i))
    (by rintro _ ⟨i, rfl⟩; exact repair_mass _ (hpos i) (hneg i)) hz
  have hrepair := repair_distance_mul (signedContrast (c i)) (signedContrast (c j)) μ hμ
    (hmargin i).1 (hmargin i).2 (hmargin j).1 (hmargin j).2
  have hcontrast := contrast_distance_le_implementation (c i) (c j)
  refine ⟨i, j, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hij (le_of_lt hμ)]

/-- For a single simplex, every pair of distinct vertices is an edge. Keeping
this premise explicit prevents replacing a local hull by a global one. -/
theorem perfect_cell_edge_jump {Vertex : Type*} (d : Vertex → PerfectCipher (Fin 4))
    (cell : Set Vertex) (Edge : Vertex → Vertex → Prop)
    (hcell : ∀ u ∈ cell, ∀ v ∈ cell, u ≠ v → Edge u v)
    (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ ((fun i => (d i).signed) '' cell)) :
    ∃ u ∈ cell, ∃ v ∈ cell, Edge u v ∧
      ∀ message, 2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨_, ⟨u, hus, rfl⟩, _, ⟨v, hvs, rfl⟩, huv⟩ := zero_convex_hull_jump
    ((fun i => (d i).signed) '' cell)
    (by rintro _ ⟨i, _, rfl⟩; exact (d i).bias_zero)
    (by rintro _ ⟨i, _, rfl⟩; exact (d i).mass_one) hz
  have hne : u ≠ v := by
    intro h
    subst v
    norm_num [l1Distance] at huv
  refine ⟨u, hus, v, hvs, hcell u hus v hvs hne, fun message => ?_⟩
  rw [perfect_jointTV]
  linarith

theorem approximate_cell_edge_jump {Vertex : Type*} (c : Vertex → Cipher (Fin 4))
    (cell : Set Vertex) (Edge : Vertex → Vertex → Prop)
    (hcell : ∀ u ∈ cell, ∀ v ∈ cell, u ≠ v → Edge u v)
    (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i ∈ cell, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i ∈ cell, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i ∈ cell, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i ∈ cell, ε i + 2 * δ i ≤ 1 - μ)
    (hz : (0 : Fin 4 → ℝ) ∈ convexHull ℝ
      ((fun i => repair (signedContrast (c i))) '' cell)) :
    ∃ u ∈ cell, ∃ v ∈ cell, Edge u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  have hrange : Set.range (fun i : cell => repair (signedContrast (c i))) =
      (fun i => repair (signedContrast (c i))) '' cell := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hz' : (0 : Fin 4 → ℝ) ∈ convexHull ℝ
      (Set.range (fun i : cell => repair (signedContrast (c i)))) := by rwa [hrange]
  obtain ⟨u, v, huv⟩ := approximate_convex_hull_jump (fun i : cell => c i)
    (fun i : cell => ε i) (fun i : cell => δ i) μ hμ
    (fun i => h0 i i.property) (fun i => h1 i i.property)
    (fun i => hp i i.property) (fun i => hm i i.property) hz'
  have hne : (u : Vertex) ≠ (v : Vertex) := by
    intro heq
    have hdist : implementationDistance (c u) (c v) = 0 := by
      rw [heq]
      simp [implementationDistance, jointTV]
    rw [hdist] at huv
    linarith
  exact ⟨u, u.property, v, v.property, hcell u u.property v v.property hne, huv⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
