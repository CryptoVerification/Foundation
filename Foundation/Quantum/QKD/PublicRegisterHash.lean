import Foundation.Quantum.QKD.PublicRegisterClassical
import Foundation.Quantum.QKD.SubnormalizedEquiv

/-! Hashing a bijectively split private key and exposing its public registers
is the same deterministic classical processing of the original accepted source.
All probabilities and every auxiliary quantum matrix entry are retained. -/
namespace Foundation.Quantum.QKD.PublicRegisterExpose
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {X A T R S K : Type} [Fintype X] [Fintype A] [Fintype T] [Fintype R] [Fintype S] [Fintype K]
  [DecidableEq A] [DecidableEq T] [DecidableEq R] [DecidableEq S] [DecidableEq K] {e : Space}

theorem split_hash_expose (ρ : State (X × R) e) (f : X ≃ (A × T)) (p : PMF S) (h : S → A → K) :
    expose (HashLayout.output (relabel (withPublic ρ) f) p h) =
      relabel (seed p ρ) (fun sx => (h sx.1 (f sx.2.1).1,(((f sx.2.1).2,sx.1),sx.2.2))) := by
  apply State.ext
  funext ⟨k,⟨⟨t,s⟩,r⟩⟩
  ext u v
  change (HashLayout.output (relabel (withPublic ρ) f) p h).block (k,(t,s))
    (Fintype.equivFin R r,u) (Fintype.equivFin R r,v) = _
  rw [HashLayout.output_block]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  have hb (a : A) : (relabel (withPublic ρ) f).block (a,t)
      (Fintype.equivFin R r,u) (Fintype.equivFin R r,v) = ρ.block (f.symm (a,t),r) u v := by
    rw [relabel_equiv_block, HashLayout.public_block]
    simp only [ite_true]
  simp_rw [hb]
  simp only [relabel, seed, Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply, Matrix.zero_apply,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and, smul_eq_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  have he (x : X) :
      (∑ s₀ : S, if h s₀ (f x).1 = k then if (f x).2 = t then
        if s₀ = s then ((p s₀).toReal:ℂ) * ρ.block (x,r) u v else 0 else 0 else 0) =
      (if h s (f x).1 = k then if (f x).2 = t then ((p s).toReal:ℂ) * ρ.block (x,r) u v else 0 else 0) := by
    have hi (s₀ : S) :
        (if h s₀ (f x).1 = k then if (f x).2 = t then
          if s₀ = s then ((p s₀).toReal:ℂ) * ρ.block (x,r) u v else 0 else 0 else 0) =
        (if s₀ = s then (if h s (f x).1 = k then if (f x).2 = t then
          ((p s).toReal:ℂ) * ρ.block (x,r) u v else 0 else 0) else 0) := by
      by_cases hs : s₀ = s
      · subst s₀; simp only [ite_true]
      · simp [hs]
    simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [he]
  have hx := f.symm.sum_comp (fun x : X => if h s (f x).1 = k then if (f x).2 = t then
    ((p s).toReal:ℂ) * ρ.block (x,r) u v else 0 else 0)
  rw [← hx]

  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : h s a = k <;> simp [ha]

end
end Foundation.Quantum.QKD.PublicRegisterExpose
