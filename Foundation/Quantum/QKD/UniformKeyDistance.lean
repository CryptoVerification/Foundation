import Foundation.Quantum.QKD.SeedDistance
import Foundation.Quantum.QKD.CommonKeyMixture

/-! Replacing a private key by fresh uniform randomness is a physical mixture
of classical channels and contracts distance while preserving side data. -/
namespace Foundation.Quantum.QKD.CommonKey
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {K T : Type} [Fintype K] [Nonempty K] [Fintype T] [DecidableEq K] [DecidableEq T] {e : Space}

theorem uniformize_random (ρ : State (K × T) e) :
    uniformize ρ = mixture (Foundation.Probability.uniform K)
      (fun k => relabel ρ (fun p => (k,p.2))) := by
  apply State.ext
  funext ⟨k,t⟩
  simp [uniformize, mixture, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and,
    Finset.smul_sum, Foundation.Probability.uniform, PMF.uniformOfFintype_apply]

theorem uniformize_approx (ρ σ : State (K × T) e) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (uniformize ρ)) (joint (uniformize σ)) ε := by
  rw [uniformize_random, uniformize_random]
  have hh := mixture_approx (Foundation.Probability.uniform K) _ _ (fun _ => ε)
    (fun k => relabel_approx ρ σ (fun p => (k,p.2)) ε h)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using hh

theorem secrecy_transfer (ρ σ : State (K × T) e) (δ ε : ℝ)
    (hclose : OperatorApprox (joint ρ) (joint σ) δ)
    (hsecret : OperatorApprox (joint σ) (joint (uniformize σ)) ε) :
    OperatorApprox (joint ρ) (joint (uniformize ρ)) (2*δ+ε) := by
  have hh := (hclose.trans hsecret).trans (uniformize_approx ρ σ δ hclose).symm
  convert hh using 1
  ring

end
end Foundation.Quantum.QKD.CommonKey
