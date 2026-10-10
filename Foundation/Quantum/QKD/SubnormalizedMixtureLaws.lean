import Foundation.Quantum.QKD.ReadClassicalState

/-! Acceptance, independent public seeds, and deterministic classical output
processing commute with the actual mixture, at original branch weights. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {S X Y U : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype U] {e : Space}

theorem mixture_restrict (p : PMF S) (ρ : S → State X e) (P : X → Prop) [DecidablePred P] :
    restrict (mixture p ρ) P = mixture p (fun s => restrict (ρ s) P) := by
  apply State.ext
  funext x
  by_cases h : P x <;> simp [restrict, mixture, h]

theorem mixture_seed (p : PMF S) (ρ : S → State X e) (q : PMF U) :
    seed q (mixture p ρ) = mixture p (fun s => seed q (ρ s)) := by
  apply State.ext
  funext ux
  simp only [seed, mixture, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem mixture_relabel [DecidableEq Y] (p : PMF S) (ρ : S → State X e) (f : X → Y) :
    relabel (mixture p ρ) f = mixture p (fun s => relabel (ρ s) f) := by
  apply State.ext
  funext y
  change (∑ x, if f x = y then ∑ s, ((p s).toReal:ℂ) • (ρ s).block x else 0) =
    ∑ s, ((p s).toReal:ℂ) • ∑ x, if f x = y then (ρ s).block x else 0
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y <;> simp [h]

end
end Foundation.Quantum.QKD.Subnormalized
