import Foundation.Quantum.QKD.SubnormalizedMixture

/-! Averaging secrecy compares with the uniform key built from the same
averaged public/quantum marginal; it does not choose a new independent marginal. -/
namespace Foundation.Quantum.QKD.CommonKey
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {S K T : Type} [Fintype S] [Fintype K] [Nonempty K] [Fintype T] {e : Space}

theorem uniformize_mixture (p : PMF S) (ρ : S → State (K × T) e) :
    mixture p (fun s => uniformize (ρ s)) = uniformize (mixture p ρ) := by
  apply State.ext
  funext x
  change (∑ s, ((p s).toReal:ℂ) • (((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, (ρ s).block (k,x.2))) =
    ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, ∑ s, ((p s).toReal:ℂ) • (ρ s).block (k,x.2)
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem mixture_secrecy [DecidableEq K] [DecidableEq T]
    (p : PMF S) (ρ : S → State (K × T) e) (ε : S → ℝ)
    (h : ∀ s, OperatorApprox (joint (ρ s)) (joint (uniformize (ρ s))) (ε s)) :
    OperatorApprox (joint (mixture p ρ)) (joint (uniformize (mixture p ρ)))
      (∑ s, (p s).toReal * ε s) := by
  have hh := mixture_approx p ρ (fun s => uniformize (ρ s)) ε h
  rw [uniformize_mixture] at hh
  exact hh

end
end Foundation.Quantum.QKD.CommonKey
