import Foundation.Quantum.Hilbert
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Heunen chapter 4 in the concrete finite Hilbert model. Predicates are
subspaces, existential transport is image, and substitution is inverse image. -/
namespace Foundation.Quantum.Predicate
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace

abbrev Pred (a : Space) := Submodule ℂ (HilbertSpace a)

def existsAlong {a b} (f : Op a b) (P : Pred a) : Pred b := P.map (Op.linear f)
def pull {a b} (f : Op a b) (Q : Pred b) : Pred a := Q.comap (Op.linear f)

theorem exists_pull {a b} (f : Op a b) (P : Pred a) (Q : Pred b) :
    existsAlong f P ≤ Q ↔ P ≤ pull f Q := Submodule.map_le_iff_le_comap

theorem orthomodular {a} {P Q : Pred a} (h : P ≤ Q) : P ⊔ Pᗮ ⊓ Q = Q :=
  Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h

def project {a} (M : Pred a) := M.starProjection.toLinearMap

def andThen {a} (P M : Pred a) : Pred a := P.map (project M)
def hook {a} (M N : Pred a) : Pred a := N.comap (project M)

theorem sasaki_adjunction {a} (P M N : Pred a) :
    andThen P M ≤ N ↔ P ≤ hook M N := Submodule.map_le_iff_le_comap

/-- Proposition 4.4.16: inverse image under a projection is the Sasaki hook. -/
theorem hook_formula {a} (M N : Pred a) : hook M N = Mᗮ ⊔ (M ⊓ N) := by
  ext x
  constructor
  · intro hx
    change M.starProjection x ∈ N at hx
    rw [Submodule.mem_sup]
    exact ⟨x - M.starProjection x, Submodule.sub_starProjection_mem_orthogonal x,
      M.starProjection x, ⟨Submodule.starProjection_apply_mem M x, hx⟩,
      sub_add_cancel _ _⟩
  · intro hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    change M.starProjection (u + v) ∈ N
    have hpu : M.starProjection u = 0 := by
      have h := (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := M)).mpr hu
      exact congrArg (fun z : M => (z : HilbertSpace a)) h
    have hpv := (Submodule.starProjection_eq_self_iff (K := M)).mpr hv.1
    rw [map_add, hpu, hpv, zero_add]
    exact hv.2

/-- The associated operation is an ordered measurement, not ordinary conjunction. -/
theorem andThen_formula {a} (P M : Pred a) : andThen P M = M ⊓ (Mᗮ ⊔ P) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Submodule.starProjection_apply_mem M y, ?_⟩
    change M.starProjection y ∈ Mᗮ ⊔ P
    apply Submodule.mem_sup.mpr
    refine ⟨-(y - M.starProjection y), Mᗮ.neg_mem
      (Submodule.sub_starProjection_mem_orthogonal y), y, hy, ?_⟩
    simp
  · rintro ⟨hx, hs⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hs
    refine ⟨v, hv, ?_⟩
    have hpu : M.starProjection u = 0 := by
      have h := (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := M)).mpr hu
      exact congrArg (fun z : M => (z : HilbertSpace a)) h
    have hpx := (Submodule.starProjection_eq_self_iff (K := M)).mpr hx
    have h := congrArg (fun z => M.starProjection z) huv
    change M.starProjection v = x
    simpa only [map_add, hpu, zero_add, hpx] using h

end
end Foundation.Quantum.Predicate
