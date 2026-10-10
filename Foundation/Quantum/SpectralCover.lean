import Foundation.Quantum.SpectralGenerators

/-! Classical finite-subcover witnesses for positive spectral opens. This
verifies the semantic compactness part of Heunen 5.2.23(b), body p.156.
The conclusion is an inequality of actual opens, not yet an inequality in
 the freely presented lattice LA; that identification remains outstanding. -/
namespace Foundation.Quantum.Bohr.Context
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CStarAlgebra A] (C : Bohr.Context A)

/-- A positive rational cut is closed and hence compact in the local spectrum. -/
theorem compact_rationalCut (a : C.algebra) (q : ℚ) :
    IsCompact {χ : C.Spectrum | (q : ℝ) ≤ (χ a).re} := by
  apply IsClosed.isCompact
  exact isClosed_le continuous_const
    (Complex.continuous_re.comp (map_continuous (WeakDual.gelfandTransform ℂ C.algebra a)))

/-- A cover of the positive part has a finite witness for every strictly
 positive rational inward shift. The intervening closed cut is essential:
 the open positive part itself need not be compact. -/
theorem finite_shift_subcover {ι : Type*} (a : C.algebra)
    (U : ι → TopologicalSpace.Opens C.Spectrum)
    (h : C.positiveOpen a ≤ ⨆ i, U i) (q : ℚ) (hq : 0 < q) :
    ∃ F : Finset ι, C.shiftedPositiveOpen a q ≤ ⨆ i ∈ F, U i := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hcover : {χ : C.Spectrum | (q : ℝ) ≤ (χ a).re} ⊆
      ⋃ i, (U i : Set C.Spectrum) := by
    intro χ hχ
    have hp : χ ∈ C.positiveOpen a := by
      change 0 < (χ a).re
      exact hq'.trans_le hχ
    have hh := h hp
    change χ ∈ (⨆ i, U i) at hh
    rw [TopologicalSpace.Opens.mem_iSup] at hh
    exact Set.mem_iUnion.mpr hh
  obtain ⟨F,hF⟩ := (C.compact_rationalCut a q).elim_finite_subcover
    (fun i => (U i : Set C.Spectrum)) (fun i => (U i).isOpen) hcover
  refine ⟨F,?_⟩
  intro χ hχ
  change 0 < (χ (a-(q:ℂ)•1)).re at hχ
  simp only [map_sub, map_smul, map_one, smul_eq_mul, mul_one, Complex.sub_re,
    Complex.ratCast_re] at hχ
  have hcut : (q : ℝ) ≤ (χ a).re := by linarith
  have hh := hF hcut
  obtain ⟨i,hi,hχi⟩ := Set.mem_iUnion₂.mp hh
  have hUi : U i ≤ ⨆ j ∈ F, U j := le_iSup₂_of_le i hi le_rfl
  exact hUi hχi

/-- Exact semantic finite-witness criterion, with no countability assumption
 on the covering family. This does not establish the free-lattice version. -/
theorem positiveOpen_cover_iff {ι : Type*} (a : C.algebra)
    (U : ι → TopologicalSpace.Opens C.Spectrum) :
    C.positiveOpen a ≤ ⨆ i, U i ↔
      ∀ q : ℚ, 0 < q → ∃ F : Finset ι, C.shiftedPositiveOpen a q ≤ ⨆ i ∈ F, U i := by
  constructor
  · intro h q hq
    exact C.finite_shift_subcover a U h q hq
  · intro h
    rw [C.positiveOpen_regular a]
    apply iSup_le
    intro q
    obtain ⟨F,hF⟩ := h q.val q.property
    exact hF.trans (iSup₂_le (fun i _ => le_iSup U i))

/-- The explicit rational separator in Heunen 5.2.19(b⇒a), verified
 as equations of local spectral opens. -/
theorem rational_separator (a : C.algebra) (q : ℚ) (hq : 0 < q) :
    C.positiveOpen a ⊔ C.positiveOpen ((q:ℂ)•1-a) = ⊤ ∧
    C.shiftedPositiveOpen a q ⊓ C.positiveOpen ((q:ℂ)•1-a) = ⊥ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · ext χ
    change (0 < (χ a).re ∨ 0 < (χ ((q:ℂ)•1-a)).re) ↔ True
    simp only [map_sub, map_smul, map_one, smul_eq_mul, mul_one, Complex.sub_re,
      Complex.ratCast_re]
    constructor
    · intro _; trivial
    · intro _
      by_cases h : 0 < (χ a).re
      · exact Or.inl h
      · exact Or.inr (by linarith)
  · ext χ
    change (0 < (χ (a-(q:ℂ)•1)).re ∧ 0 < (χ ((q:ℂ)•1-a)).re) ↔ False
    simp only [map_sub, map_smul, map_one, smul_eq_mul, mul_one, Complex.sub_re,
      Complex.ratCast_re]
    constructor
    · rintro ⟨h,h'⟩
      linarith
    · exact False.elim

/-- Each inward shift is well inside the positive open: an actual separator
 covers with the larger open and is disjoint from the smaller one. -/
theorem shifted_well_inside (a : C.algebra) (q : ℚ) (hq : 0 < q) :
    ∃ W : TopologicalSpace.Opens C.Spectrum,
      W ⊔ C.positiveOpen a = ⊤ ∧ W ⊓ C.shiftedPositiveOpen a q = ⊥ := by
  refine ⟨C.positiveOpen ((q:ℂ)•1-a),?_,?_⟩
  · simpa only [sup_comm] using (C.rational_separator a q hq).1
  · simpa only [inf_comm] using (C.rational_separator a q hq).2

/-- Increasing the inward shift can only decrease the open. -/
theorem shiftedPositiveOpen_antitone (a : C.algebra) {q r : ℚ} (h : q ≤ r) :
    C.shiftedPositiveOpen a r ≤ C.shiftedPositiveOpen a q := by
  intro χ hχ
  change 0 < (χ (a-(r:ℂ)•1)).re at hχ
  change 0 < (χ (a-(q:ℂ)•1)).re
  simp only [map_sub, map_smul, map_one, smul_eq_mul, mul_one, Complex.sub_re,
    Complex.ratCast_re] at *
  have h' : (q : ℝ) ≤ r := by exact_mod_cast h
  linarith

/-- A compact subset of a positive open stays inside one positive rational
 inward shift, obtained from a finite cover of that compact subset. -/
theorem compact_subset_shift (a : C.algebra) (K : Set C.Spectrum)
    (hK : IsCompact K) (hsub : K ⊆ C.positiveOpen a) :
    ∃ q : {q : ℚ // 0 < q}, K ⊆ C.shiftedPositiveOpen a q.val := by
  have hcover : K ⊆ ⋃ q : {q : ℚ // 0 < q},
      (C.shiftedPositiveOpen a q.val : Set C.Spectrum) := by
    intro χ hχ
    have hh := hsub hχ
    change χ ∈ C.positiveOpen a at hh
    rw [C.positiveOpen_regular, TopologicalSpace.Opens.mem_iSup] at hh
    exact Set.mem_iUnion.mpr hh
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover
    (fun q : {q : ℚ // 0 < q} => (C.shiftedPositiveOpen a q.val : Set C.Spectrum))
    (fun q => (C.shiftedPositiveOpen a q.val).isOpen) hcover
  let F' := insert (⟨1,by norm_num⟩ : {q : ℚ // 0 < q}) F
  have hne : F'.Nonempty := Finset.insert_nonempty _ _
  let q := F'.min' hne
  refine ⟨q,?_⟩
  intro χ hχ
  obtain ⟨r,hr,hχr⟩ := Set.mem_iUnion₂.mp (hF hχ)
  have hqr : q ≤ r := Finset.min'_le F' r (Finset.mem_insert_of_mem hr)
  exact C.shiftedPositiveOpen_antitone a hqr hχr

/-- The classical semantic version of Heunen 5.2.19, with an arbitrary open
 as the smaller proposition. The free-lattice version is still separate. -/
theorem well_inside_positive_iff (a : C.algebra) (U : TopologicalSpace.Opens C.Spectrum) :
    (∃ W : TopologicalSpace.Opens C.Spectrum,
      W ⊔ C.positiveOpen a = ⊤ ∧ W ⊓ U = ⊥) ↔
    ∃ q : {q : ℚ // 0 < q}, U ≤ C.shiftedPositiveOpen a q.val := by
  constructor
  · rintro ⟨W,hcover,hdisj⟩
    have hK : IsCompact (W : Set C.Spectrum)ᶜ := W.isOpen.isClosed_compl.isCompact
    have hsub : (W : Set C.Spectrum)ᶜ ⊆ C.positiveOpen a := by
      intro χ hχ
      have hh : χ ∈ W ⊔ C.positiveOpen a := by rw [hcover]; trivial
      change χ ∈ W ∨ χ ∈ C.positiveOpen a at hh
      exact hh.resolve_left hχ
    obtain ⟨q,hq⟩ := C.compact_subset_shift a _ hK hsub
    refine ⟨q,?_⟩
    intro χ hχ
    apply hq
    intro hw
    have hh : χ ∈ W ⊓ U := ⟨hw,hχ⟩
    rw [hdisj] at hh
    exact hh
  · rintro ⟨q,hq⟩
    obtain ⟨W,hw,hwu⟩ := C.shifted_well_inside a q.val q.property
    refine ⟨W,hw,?_⟩
    apply le_antisymm
    · exact (inf_le_inf_left W hq).trans (le_of_eq hwu)
    · exact bot_le

end
end Foundation.Quantum.Bohr.Context
