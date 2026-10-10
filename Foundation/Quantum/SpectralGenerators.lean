import Foundation.Quantum.ContextSpectrum

/-! Heunen §5.2.10, relations (5.3)–(5.8), body pp.152–153:
verified in the actual local character spectra. These are the geometric
relations needed for the constructive presentation; their universal property
and internal Gelfand duality are not assumed here. -/
namespace Foundation.Quantum.Bohr.Context
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CStarAlgebra A] (C : Context A)

/-- Characters take real values on self-adjoint observables. -/
theorem character_im_zero (χ : C.Spectrum) (a : C.algebra) (ha : IsSelfAdjoint a) :
    (χ a).im = 0 := by
  apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
  exact ha.map χ

/-- Relation (5.4). -/
theorem positiveOpen_neg_disjoint (a : C.algebra) :
    C.positiveOpen a ⊓ C.positiveOpen (-a) = ⊥ := by
  ext χ
  change (0 < (χ a).re ∧ 0 < (χ (-a)).re) ↔ False
  simp only [map_neg, Complex.neg_re]
  constructor
  · rintro ⟨h,h'⟩
    linarith
  · exact False.elim

/-- Relation (5.5), with the original self-adjoint hypothesis. -/
theorem positiveOpen_neg_square (b : C.algebra) (hb : IsSelfAdjoint b) :
    C.positiveOpen (-(b*b)) = ⊥ := by
  ext χ
  have him := C.character_im_zero χ b hb
  change 0 < (χ (-(b*b))).re ↔ False
  simp only [map_neg, map_mul, Complex.neg_re, Complex.mul_re, him, zero_mul, sub_zero]
  constructor
  · intro h
    nlinarith [sq_nonneg (χ b).re]
  · exact False.elim

/-- Relation (5.6). -/
theorem positiveOpen_add_le (a b : C.algebra) :
    C.positiveOpen (a+b) ≤ C.positiveOpen a ⊔ C.positiveOpen b := by
  intro χ h
  change 0 < (χ (a+b)).re at h
  change 0 < (χ a).re ∨ 0 < (χ b).re
  rw [map_add, Complex.add_re] at h
  by_contra hn
  push Not at hn
  linarith

/-- Relation (5.7); self-adjointness is essential for the sign-of-product calculation. -/
theorem positiveOpen_mul (a b : C.algebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    C.positiveOpen (a*b) =
      (C.positiveOpen a ⊓ C.positiveOpen b) ⊔ (C.positiveOpen (-a) ⊓ C.positiveOpen (-b)) := by
  ext χ
  have hia := C.character_im_zero χ a ha
  have hib := C.character_im_zero χ b hb
  change 0 < (χ (a*b)).re ↔
    (0 < (χ a).re ∧ 0 < (χ b).re) ∨ (0 < (χ (-a)).re ∧ 0 < (χ (-b)).re)
  simp only [map_mul, map_neg, Complex.mul_re, Complex.neg_re, hia, hib, zero_mul, sub_zero]
  simpa only [neg_pos] using (mul_pos_iff (a := (χ a).re) (b := (χ b).re))

/-- The rational positive shifts appearing in the regularity relation (5.8). -/
def shiftedPositiveOpen (a : C.algebra) (q : ℚ) : TopologicalSpace.Opens C.Spectrum :=
  C.positiveOpen (a - (q : ℂ) • 1)

/-- Equality strengthens the generating-cover inclusion (5.8) in the classical local model. -/
theorem positiveOpen_regular (a : C.algebra) :
    C.positiveOpen a = ⨆ q : {q : ℚ // 0 < q}, C.shiftedPositiveOpen a q.val := by
  ext χ
  change χ ∈ C.positiveOpen a ↔ χ ∈ (⨆ q : {q : ℚ // 0 < q}, C.shiftedPositiveOpen a q.val)
  rw [TopologicalSpace.Opens.mem_iSup]
  change 0 < (χ a).re ↔ ∃ q : {q : ℚ // 0 < q}, 0 < (χ (a - (q.val : ℂ) • 1)).re
  simp only [map_sub, map_smul, map_one, smul_eq_mul, mul_one, Complex.sub_re,
    Complex.ratCast_re]
  constructor
  · intro h
    obtain ⟨q,hq0,hq⟩ := exists_rat_btwn h
    have hqpos : (0 : ℚ) < q := by exact_mod_cast hq0
    refine ⟨⟨q,hqpos⟩, ?_⟩
    change 0 < (χ a).re - (q : ℝ)
    linarith
  · rintro ⟨q,hq⟩
    have hq0 : (0 : ℝ) < q.val := by exact_mod_cast q.property
    linarith

end
end Foundation.Quantum.Bohr.Context
