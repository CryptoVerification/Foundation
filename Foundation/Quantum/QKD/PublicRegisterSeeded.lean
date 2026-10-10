import Foundation.Quantum.QKD.PublicRegisterHash

/-! Expose an existing classical register after arbitrary seeded classical
processing. The full quantum slices agree, without any injectivity premise. -/
namespace Foundation.Quantum.QKD.PublicRegisterExpose
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {X R S K L : Type} [Fintype X] [Fintype R] [Fintype S] [Fintype K] [Fintype L]
  [DecidableEq K] [DecidableEq L] [DecidableEq R] {e : Space}

theorem expose_seed_relabel (ρ : State (X × R) e) (p : PMF S) (f : S × X → K × L) :
    expose (relabel (seed p (withPublic ρ)) f) =
      relabel (seed p ρ) (fun sx => ((f (sx.1,sx.2.1)).1,((f (sx.1,sx.2.1)).2,sx.2.2))) := by
  apply State.ext
  funext ⟨k,l,r⟩
  ext u v
  change (relabel (seed p (withPublic ρ)) f).block (k,l)
    (Fintype.equivFin R r,u) (Fintype.equivFin R r,v) = _
  simp only [relabel, seed, Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply,
    Matrix.zero_apply, Fintype.sum_prod_type, smul_eq_mul]
  have hb (x : X) := HashLayout.public_block ρ x r r u v
  simp only [ite_true] at hb
  simp_rw [hb]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  simp only [Prod.ext_iff, ite_and]
  by_cases hk : (f (s,x)).1 = k <;> by_cases hl : (f (s,x)).2 = l <;>
    simp [hk,hl]

end
end Foundation.Quantum.QKD.PublicRegisterExpose
