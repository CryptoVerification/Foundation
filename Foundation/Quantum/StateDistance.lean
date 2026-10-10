import Foundation.Quantum.Mixture
import Foundation.Quantum.Distinguishability

/-! Observational distance of whole joint states. In a QKD application these
states include keys, abort, public transcript and the adversary's subsystem.
A bound on a reduced Eve marginal alone is not substituted for this property. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every binary physical observation distinguishes the two states by at most ε. -/
def StateApprox {a : Space} (ρ σ : Density a) (ε : ℝ) : Prop :=
  ∀ E : Effect a, |E.probability ρ - E.probability σ| ≤ ε

namespace StateApprox
variable {a b : Space} {ρ σ τ : Density a} {ε δ : ℝ}

/-- Existing auxiliary-system-complete channel bounds imply bounds on each actual joint output state. -/
theorem of_channel {x y : Space} {C D : Channel x y} (h : Approx C D ε)
    (e : Space) (input : Density (.tensor x e)) :
    StateApprox ((C.amplify e).run input) ((D.amplify e).run input) ε := h e input

theorem refl (ρ : Density a) : StateApprox ρ ρ 0 := by intro E; simp

theorem symm (h : StateApprox ρ σ ε) : StateApprox σ ρ ε := by
  intro E
  simpa only [abs_sub_comm] using h E

theorem trans (h : StateApprox ρ σ ε) (g : StateApprox σ τ δ) : StateApprox ρ τ (ε + δ) := by
  intro E
  calc
    _ ≤ |E.probability ρ - E.probability σ| + |E.probability σ - E.probability τ| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h E) (g E)

theorem postprocess (C : Channel a b) (h : StateApprox ρ σ ε) :
    StateApprox (C.run ρ) (C.run σ) ε := by
  intro E
  simpa only [Effect.probability_run] using h (C.pullEffect E)

theorem weaken (h : StateApprox ρ σ ε) (hεδ : ε ≤ δ) : StateApprox ρ σ δ :=
  fun E => (h E).trans hεδ

/-- Conditional errors are averaged with the actual distribution of the public randomness. -/
theorem mixture {ι : Type*} [Fintype ι] (p : PMF ι) (ρ σ : ι → Density a) (ε : ι → ℝ)
    (h : ∀ i, StateApprox (ρ i) (σ i) (ε i)) :
    StateApprox (Density.mixture p ρ) (Density.mixture p σ) (∑ i, (p i).toReal * ε i) := by
  intro E
  rw [Density.mixture_observation, Density.mixture_observation, ← Finset.sum_sub_distrib]
  calc
    _ = |∑ i, (p i).toReal * (E.probability (ρ i) - E.probability (σ i))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |(p i).toReal * (E.probability (ρ i) - E.probability (σ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (p i).toReal * |E.probability (ρ i) - E.probability (σ i)| := by
      simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i E) ENNReal.toReal_nonneg)

theorem mixture_uniform_bound {ι : Type*} [Fintype ι] (p : PMF ι) (ρ σ : ι → Density a)
    (h : ∀ i, StateApprox (ρ i) (σ i) ε) :
    StateApprox (Density.mixture p ρ) (Density.mixture p σ) ε := by
  have hb := mixture p ρ σ (fun _ => ε) h
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using hb

end StateApprox
end
end Foundation.Quantum
