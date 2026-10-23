import Foundation.Crypto.Semantics.Probability.ClassicalBitConvexCertificate

/-! Nonnull boundary certificates force a zero of an interior interpolation,
and hence a large edge in a covered cell. Boundary nonnullity and the
interpolation's cell-cover property are explicit premises, not new axioms. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Key : Type*} [Fintype Key]

abbrev PerfectVector (Key : Type*) [Fintype Key] :=
  {w : Key → ℝ // bias w = 0 ∧ mass w = 1}

def normalizeSigned (w : Key → ℝ) (i : Key) : ℝ := w i / mass w

theorem mass_pos_of_ne_zero (w : Key → ℝ) (hw : w ≠ 0) : 0 < mass w := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hle : |w i| ≤ mass w :=
    Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (abs_pos.mpr hi) hle

theorem normalizeSigned_bias (w : Key → ℝ) (hw : bias w = 0) :
    bias (normalizeSigned w) = 0 := by
  unfold bias normalizeSigned
  rw [← Finset.sum_div]
  change bias w / mass w = 0
  rw [hw, zero_div]

theorem normalizeSigned_mass (w : Key → ℝ) (hw : w ≠ 0) :
    mass (normalizeSigned w) = 1 := by
  have hm := mass_pos_of_ne_zero w hw
  unfold mass normalizeSigned
  simp_rw [abs_div, abs_of_pos hm]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hm)

theorem normalizeSigned_fixed (w : Key → ℝ) (hw : mass w = 1) :
    normalizeSigned w = w := by
  funext i
  simp [normalizeSigned, hw]

/-- Abstract boundary theorem, independent of a particular sphere classification.
It is essential that boundary nonnullity is proved in the same perfect-vector
space, including its convention on labels and zero-weight branches. -/
theorem nonnull_boundary_forces_zero {X Boundary : Type*}
    [TopologicalSpace X] [ContractibleSpace X] [TopologicalSpace Boundary]
    (boundary : C(Boundary, X)) (f : C(Boundary, PerfectVector Key))
    (hnonnull : ¬f.Nullhomotopic) (F : C(X, Key → ℝ))
    (hzero : ∀ x, bias (F x) = 0)
    (hboundary : ∀ s, F (boundary s) = (f s).val) :
    ∃ x, F x = 0 := by
  by_contra h
  push Not at h
  have hm (x : X) : 0 < mass (F x) := mass_pos_of_ne_zero (F x) (h x)
  have hc : Continuous (fun x => mass (F x)) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp F.continuous).abs
  have hnorm : Continuous (fun x => normalizeSigned (F x)) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp F.continuous).div hc (fun x => ne_of_gt (hm x))
  let g : C(X, PerfectVector Key) :=
    ⟨fun x => ⟨normalizeSigned (F x), normalizeSigned_bias _ (hzero x),
       normalizeSigned_mass _ (h x)⟩, hnorm.subtype_mk _⟩
  have heq : g.comp boundary = f := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    change normalizeSigned (F (boundary s)) = (f s).val
    rw [hboundary, normalizeSigned_fixed _ (f s).property.2]
  have hnull : g.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic X).comp_right g
  apply hnonnull
  rw [← heq]
  exact hnull.comp_left boundary

/-- The covered-cell premise is local: at each interpolation point some single
cell contains it in its convex hull, and distinct vertices of that cell are edges. -/
theorem nonnull_boundary_forces_perfect_edge {X Boundary Vertex : Type*}
    [TopologicalSpace X] [ContractibleSpace X] [TopologicalSpace Boundary]
    (boundary : C(Boundary, X)) (f : C(Boundary, PerfectVector (Fin 4)))
    (hnonnull : ¬f.Nullhomotopic) (F : C(X, Fin 4 → ℝ))
    (hzero : ∀ x, bias (F x) = 0)
    (hboundary : ∀ s, F (boundary s) = (f s).val)
    (d : Vertex → PerfectCipher (Fin 4)) (Edge : Vertex → Vertex → Prop)
    (hcover : ∀ x, ∃ cell : Set Vertex,
      (∀ u ∈ cell, ∀ v ∈ cell, u ≠ v → Edge u v) ∧
      F x ∈ convexHull ℝ ((fun i => (d i).signed) '' cell)) :
    ∃ u v, Edge u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨x, hx⟩ := nonnull_boundary_forces_zero boundary f hnonnull F hzero hboundary
  obtain ⟨cell, hcell, hmem⟩ := hcover x
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := perfect_cell_edge_jump d cell Edge hcell hmem
  exact ⟨u, v, huv, hdist⟩

theorem nonnull_boundary_forces_approximate_edge {X Boundary Vertex : Type*}
    [TopologicalSpace X] [ContractibleSpace X] [TopologicalSpace Boundary]
    (boundary : C(Boundary, X)) (f : C(Boundary, PerfectVector (Fin 4)))
    (hnonnull : ¬f.Nullhomotopic) (F : C(X, Fin 4 → ℝ))
    (hzero : ∀ x, bias (F x) = 0)
    (hboundary : ∀ s, F (boundary s) = (f s).val)
    (c : Vertex → Cipher (Fin 4)) (Edge : Vertex → Vertex → Prop)
    (ε δ : Vertex → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (hcover : ∀ x, ∃ cell : Set Vertex,
      (∀ u ∈ cell, ∀ v ∈ cell, u ≠ v → Edge u v) ∧
      F x ∈ convexHull ℝ ((fun i => repair (signedContrast (c i))) '' cell)) :
    ∃ u v, Edge u v ∧ μ / 3 ≤ implementationDistance (c u) (c v) := by
  obtain ⟨x, hx⟩ := nonnull_boundary_forces_zero boundary f hnonnull F hzero hboundary
  obtain ⟨cell, hcell, hmem⟩ := hcover x
  rw [hx] at hmem
  obtain ⟨u, _, v, _, huv, hdist⟩ := approximate_cell_edge_jump c cell Edge hcell
    ε δ μ hμ (fun i _ => h0 i) (fun i _ => h1 i)
    (fun i _ => hp i) (fun i _ => hm i) hmem
  exact ⟨u, v, huv, hdist⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
