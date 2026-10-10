import Foundation.Quantum.QKD.SubnormalizedDistance
import Foundation.Quantum.QKD.SeededSubnormalized

/-! Fresh independent classical randomness cannot increase observation
distance, even on subnormalized accepted branches. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {S X : Type} [Fintype S] [Fintype X] [DecidableEq S] [DecidableEq X] {e : Space}

theorem seed_mixture (p : PMF S) (ρ : State X e) :
    seed p ρ = mixture p (fun s => relabel ρ (fun x => (s,x))) := by
  apply State.ext
  funext ⟨s,x⟩
  simp [seed, mixture, relabel, Prod.mk.injEq, ite_and, Finset.smul_sum]

theorem seed_approx (p : PMF S) (ρ σ : State X e) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (seed p ρ)) (joint (seed p σ)) ε := by
  rw [seed_mixture, seed_mixture]
  have hh := mixture_approx p _ _ (fun _ => ε) (fun s => relabel_approx ρ σ (fun x => (s,x)) ε h)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using hh

end
end Foundation.Quantum.QKD.Subnormalized
