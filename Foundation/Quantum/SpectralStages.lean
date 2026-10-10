import Foundation.Quantum.ContextSpectrum
import Mathlib.Order.Category.Frm
import Mathlib.Order.CompleteLatticeIntervals

/-! External stage frames of the spectral bundle. At C we retain precisely
opens over future contexts D≥C, and context extension truncates this family.
This implements the stage/truncation structure of Heunen 5.3.16; identification
with the internally presented spectrum still requires the covering theorem. -/
namespace Foundation.Quantum.Bohr
noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CStarAlgebra A]

/-- The open part of the bundle over the principal upward set of contexts. -/
def contextOpen (C : Context A) : SpectralOpen A where
  carrier := {p | C ≤ p.1}
  is_open' := ⟨by
    intro D
    by_cases h : C ≤ D
    · simp [h]
    · simp [h],
    fun D E h χ hx => hx.trans h⟩

theorem contextOpen_antitone {C D : Context A} (h : C ≤ D) : contextOpen D ≤ contextOpen C :=
  fun _ hp => h.trans hp

/-- Opens restricted to contexts above C, realized as an interval of the global frame. -/
abbrev StageFrame (C : Context A) := Set.Iic (contextOpen C)

instance stageFrame (C : Context A) : Order.Frame (StageFrame C) :=
  Order.Frame.ofMinimalAxioms {
    inf_sSup_le_iSup_inf := by
      intro U S
      change U.val ⊓ (sSup S : StageFrame C).val ≤ (⨆ V ∈ S, U ⊓ V : StageFrame C).val
      simp only [Set.Iic.coe_sSup, Set.Iic.coe_iSup, Set.Iic.coe_inf]
      rw [inf_sSup_eq]
      apply iSup₂_le
      intro V hV
      obtain ⟨W,hW,rfl⟩ := hV
      exact le_iSup₂_of_le W hW le_rfl }

def truncate {C D : Context A} (_h : C ≤ D) (U : StageFrame C) : StageFrame D :=
  ⟨U.val ⊓ contextOpen D, by change U.val ⊓ contextOpen D ≤ contextOpen D; exact inf_le_right⟩

/-- Truncation is a genuine frame morphism, preserving arbitrary joins and finite meets. -/
def stageRestriction {C D : Context A} (h : C ≤ D) : FrameHom (StageFrame C) (StageFrame D) where
  toFun := truncate h
  map_top' := by
    apply Subtype.ext
    change contextOpen C ⊓ contextOpen D = contextOpen D
    exact inf_eq_right.mpr (contextOpen_antitone h)
  map_inf' U V := by
    apply Subtype.ext
    change (U.val ⊓ V.val) ⊓ contextOpen D =
      (U.val ⊓ contextOpen D) ⊓ (V.val ⊓ contextOpen D)
    simp only [inf_inf_inf_comm, inf_idem]
  map_sSup' S := by
    apply Subtype.ext
    change (sSup S : StageFrame C).val ⊓ contextOpen D =
      (sSup (truncate h '' S) : StageFrame D).val
    rw [Set.Iic.coe_sSup, Set.Iic.coe_sSup, Set.image_image, sSup_image, sSup_image, iSup_inf_eq]
    simp_rw [iSup_inf_eq]
    rfl

@[simp] theorem stageRestriction_id (C : Context A) :
    stageRestriction (le_refl C) = FrameHom.id (StageFrame C) := by
  apply FrameHom.ext
  intro U
  apply Subtype.ext
  exact inf_eq_left.mpr U.property

theorem stageRestriction_comp {C D E : Context A} (h : C ≤ D) (k : D ≤ E) :
    stageRestriction (h.trans k) = (stageRestriction k).comp (stageRestriction h) := by
  apply FrameHom.ext
  intro U
  apply Subtype.ext
  change U.val ⊓ contextOpen E = (U.val ⊓ contextOpen D) ⊓ contextOpen E
  rw [inf_assoc, inf_eq_right.mpr (contextOpen_antitone k)]

/-- A covariant diagram of stage frames; the opposing locale maps restrict the domain of contexts. -/
def spectralFrameDiagram (A : Type) [CStarAlgebra A] : Context A ⥤ Frm where
  obj C := Frm.of (StageFrame C)
  map f := Frm.ofHom (stageRestriction (leOfHom f))
  map_id C := by
    apply Frm.Hom.ext
    exact stageRestriction_id C
  map_comp f g := by
    apply Frm.Hom.ext
    exact stageRestriction_comp (leOfHom f) (leOfHom g)

/-- The action on any future context is literally truncation, not a different local spectrum. -/
theorem stageRestriction_fiber {C D E : Context A} (h : C ≤ D) (hDE : D ≤ E)
    (U : StageFrame C) : (stageRestriction h U).val.fiber E = U.val.fiber E := by
  ext χ
  change ((⟨E,χ⟩ : SpectrumBundle A) ∈ U.val ∧ D ≤ E) ↔ (⟨E,χ⟩ : SpectrumBundle A) ∈ U.val
  simp only [hDE, and_true]

/-- A stage has no truth at a context outside its upward domain. -/
theorem stage_outside {C D : Context A} (h : ¬ C ≤ D) (U : StageFrame C) : U.val.fiber D = ⊥ := by
  ext χ
  change (⟨D,χ⟩ : SpectrumBundle A) ∈ U.val ↔ False
  exact ⟨fun hx => h (U.property hx), False.elim⟩

/-- Implication in a stage is relative to the upward domain of that stage. -/
theorem stage_himp_val (C : Context A) (U V : StageFrame C) :
    (U ⇨ V).val = (U.val ⇨ V.val) ⊓ contextOpen C := by
  let W : StageFrame C := ⟨(U.val ⇨ V.val) ⊓ contextOpen C, by
    change (U.val ⇨ V.val) ⊓ contextOpen C ≤ contextOpen C
    exact inf_le_right⟩
  have hw : W ⊓ U ≤ V := by
    change ((U.val ⇨ V.val) ⊓ contextOpen C) ⊓ U.val ≤ V.val
    exact (inf_le_inf_right U.val inf_le_left).trans (le_himp_iff.mp le_rfl)
  have hwu : W ≤ U ⇨ V := le_himp_iff.mpr hw
  apply le_antisymm
  · apply le_inf
    · apply le_himp_iff.mpr
      have hv : (U ⇨ V) ⊓ U ≤ V := le_himp_iff.mp le_rfl
      exact hv
    · exact (U ⇨ V).property
  · exact hwu

/-- Restriction to an open future domain preserves relative implication. -/
theorem stageRestriction_himp {C D : Context A} (h : C ≤ D) (U V : StageFrame C) :
    stageRestriction h (U ⇨ V) = stageRestriction h U ⇨ stageRestriction h V := by
  apply le_antisymm
  · apply le_himp_iff.mpr
    have hUV : (U ⇨ V) ⊓ U ≤ V := le_himp_iff.mp le_rfl
    simpa only [map_inf] using OrderHomClass.mono (stageRestriction h) hUV
  · change (stageRestriction h U ⇨ stageRestriction h V).val ≤ (U ⇨ V).val ⊓ contextOpen D
    apply le_inf
    · rw [stage_himp_val C U V]
      apply le_inf
      · apply le_himp_iff.mpr
        have hUV : (stageRestriction h U ⇨ stageRestriction h V) ⊓ stageRestriction h U ≤
            stageRestriction h V := le_himp_iff.mp le_rfl
        change (stageRestriction h U ⇨ stageRestriction h V).val ⊓ (U.val ⊓ contextOpen D) ≤
          V.val ⊓ contextOpen D at hUV
        have hdom : (stageRestriction h U ⇨ stageRestriction h V).val ≤ contextOpen D :=
          (stageRestriction h U ⇨ stageRestriction h V).property
        calc
          (stageRestriction h U ⇨ stageRestriction h V).val ⊓ U.val =
              (stageRestriction h U ⇨ stageRestriction h V).val ⊓ (U.val ⊓ contextOpen D) := by
                calc
                  _ = ((stageRestriction h U ⇨ stageRestriction h V).val ⊓ contextOpen D) ⊓ U.val :=
                    congrArg (fun X => X ⊓ U.val) (inf_eq_left.mpr hdom).symm
                  _ = _ := by ac_rfl
          _ ≤ V.val := hUV.trans inf_le_left
      · exact (stageRestriction h U ⇨ stageRestriction h V).property.trans (contextOpen_antitone h)
    · exact (stageRestriction h U ⇨ stageRestriction h V).property

end
end Foundation.Quantum.Bohr
