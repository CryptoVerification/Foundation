import Foundation.Quantum.QKD.HashLayout

/-! Expose an already classical register in the side system as an explicit
public label. No auxiliary quantum matrix entries are discarded. -/
namespace Foundation.Quantum.QKD.PublicRegisterExpose
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {K L R : Type} [Fintype K] [Fintype L] [Fintype R] {e : Space}

def Diagonal [DecidableEq R] {X : Type} [Fintype X] (ρ : State X (Guessing.publicSpace R e)) : Prop :=
  ∀ x r s (u v : e.Basis), ρ.block x (Fintype.equivFin R r,u) (Fintype.equivFin R s,v) =
    if r = s then ρ.block x (Fintype.equivFin R r,u) (Fintype.equivFin R r,v) else 0

theorem trace_slices (A : Operator (Guessing.publicSpace R e)) :
    (∑ r : R, (A.submatrix (fun u => (Fintype.equivFin R r,u))
      (fun u => (Fintype.equivFin R r,u))).trace) = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Fintype.sum_prod_type]
  exact (Fintype.equivFin R).sum_comp (fun r => ∑ u, A (r,u) (r,u))

def expose (ρ : State (K × L) (Guessing.publicSpace R e)) : State (K × (L × R)) e where
  block p := (ρ.block (p.1,p.2.1)).submatrix
    (fun u => (Fintype.equivFin R p.2.2,u)) (fun u => (Fintype.equivFin R p.2.2,u))
  positive p := (ρ.positive _).submatrix _
  bounded := by
    simp only [Fintype.sum_prod_type]
    simp_rw [← Complex.re_sum, trace_slices]
    simpa only [Fintype.sum_prod_type, Complex.re_sum] using ρ.bounded

def basis : (Guessing.publicSpace (K × (L × R)) e).Basis ≃
    (Guessing.publicSpace (K × L) (Guessing.publicSpace R e)).Basis where
  toFun i := let p := (Fintype.equivFin (K × (L × R))).symm i.1
    (Fintype.equivFin (K × L) (p.1,p.2.1),(Fintype.equivFin R p.2.2,i.2))
  invFun i := let p := (Fintype.equivFin (K × L)).symm i.1
    (Fintype.equivFin (K × (L × R)) (p.1,(p.2,(Fintype.equivFin R).symm i.2.1)),i.2.2)
  left_inv i := by simp
  right_inv i := by simp

theorem joint_expose [DecidableEq K] [DecidableEq L] [DecidableEq R]
    (ρ : State (K × L) (Guessing.publicSpace R e)) (hρ : Diagonal ρ) :
    BasisTransport.operator (basis (K := K) (L := L) (R := R) (e := e)) (joint ρ) = joint (expose ρ) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨k,l,r⟩,rfl⟩ := (Fintype.equivFin (K × (L × R))).surjective i
  obtain ⟨⟨k',l',r'⟩,rfl⟩ := (Fintype.equivFin (K × (L × R))).surjective j
  change joint ρ (basis (K := K) (L := L) (R := R) (e := e) (Fintype.equivFin _ (k,(l,r)),u))
      (basis (K := K) (L := L) (R := R) (e := e) (Fintype.equivFin _ (k',(l',r')),v)) = _
  simp only [basis, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rw [joint_block, joint_block]
  rw [hρ]
  by_cases hk : k = k' <;> by_cases hl : l = l' <;> by_cases hr : r = r' <;>
    simp [hk, hl, hr, expose, Prod.mk.injEq, Matrix.submatrix_apply]

variable [Nonempty K]

theorem uniformize_expose [DecidableEq K] [DecidableEq L] [DecidableEq R]
    (ρ : State (K × L) (Guessing.publicSpace R e)) :
    expose (CommonKey.uniformize ρ) = CommonKey.uniformize (expose ρ) := by
  apply State.ext
  funext p
  ext u v
  simp only [expose, CommonKey.uniformize, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply]

theorem uniformize_diagonal [DecidableEq K] [DecidableEq L] [DecidableEq R]
    (ρ : State (K × L) (Guessing.publicSpace R e)) (hρ : Diagonal ρ) :
    Diagonal (CommonKey.uniformize ρ) := by
  intro ⟨k,l⟩ r s u v
  simp only [CommonKey.uniformize, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have hd (k' : K) := hρ (k',l) r s u v
  simp_rw [hd]
  by_cases h : r = s <;> simp [h]

theorem secrecy [DecidableEq K] [DecidableEq L] [DecidableEq R]
    (ρ : State (K × L) (Guessing.publicSpace R e)) (hρ : Diagonal ρ) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint (CommonKey.uniformize ρ)) ε) :
    OperatorApprox (joint (expose ρ)) (joint (CommonKey.uniformize (expose ρ))) ε := by
  have hh := BasisTransport.approx (basis (K := K) (L := L) (R := R) (e := e)) _ _ ε h
  rw [joint_expose ρ hρ, joint_expose _ (uniformize_diagonal ρ hρ), uniformize_expose] at hh
  exact hh

end
end Foundation.Quantum.QKD.PublicRegisterExpose
