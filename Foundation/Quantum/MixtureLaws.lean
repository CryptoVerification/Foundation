import Foundation.Quantum.Mixture

/-! Finite probability identities for actual joint density matrices. -/
namespace Foundation.Quantum.Density
noncomputable section
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a : Space}

theorem mixture_congr_matrix (p : PMF ι) (ρ σ : ι → Density a)
    (h : ∀ i, (ρ i).matrix = (σ i).matrix) :
    (mixture p ρ).matrix = (mixture p σ).matrix := by
  unfold mixture
  simp_rw [h]

theorem mixture_bind (p : PMF ι) (q : ι → PMF κ) (ρ : κ → Density a) :
    (mixture (p.bind q) ρ).matrix =
      (mixture p (fun i => mixture (q i) ρ)).matrix := by
  have weight (j : κ) : (((p.bind q) j).toReal : ℂ) =
      ∑ i, ((p i).toReal : ℂ) * ((q i j).toReal : ℂ) := by
    rw [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (p.apply_ne_top i) ((q i).apply_ne_top j))]
    simp only [ENNReal.toReal_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [mixture, weight, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem mixture_pure (i : ι) (ρ : ι → Density a) :
    (mixture (PMF.pure i) ρ).matrix = (ρ i).matrix := by
  classical
  simp [mixture, PMF.pure_apply, apply_ite]

theorem mixture_map (p : PMF ι) (f : ι → κ) (ρ : κ → Density a) :
    (mixture (p.map f) ρ).matrix = (mixture p (fun i => ρ (f i))).matrix := by
  rw [PMF.map, mixture_bind]
  change (∑ i, ((p i).toReal : ℂ) • (mixture (PMF.pure (f i)) ρ).matrix) = _
  simp only [mixture_pure]
  rfl

theorem mixture_uniform_equiv [Nonempty ι] [Nonempty κ] (e : ι ≃ κ) (ρ : κ → Density a) :
    (mixture (uniform ι) (fun i => ρ (e i))).matrix =
      (mixture (uniform κ) ρ).matrix := by
  simp only [mixture, uniform, PMF.uniformOfFintype_apply, Fintype.card_congr e]
  exact Equiv.sum_comp e (fun j =>
    (((Fintype.card κ : ℝ≥0∞)⁻¹).toReal : ℂ) • (ρ j).matrix)

theorem mixture_uniform_product [Nonempty ι] [Nonempty κ] (ρ : ι × κ → Density a) :
    (mixture (uniform (ι × κ)) ρ).matrix =
      (mixture (uniform ι) (fun i => mixture (uniform κ) (fun j => ρ (i,j)))).matrix := by
  have weight (i : ι) (j : κ) : (((uniform (ι × κ) (i,j)).toReal : ℝ) : ℂ) =
      ((uniform ι i).toReal : ℂ) * ((uniform κ j).toReal : ℂ) := by
    simp [uniform, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm]
  simp only [mixture, Fintype.sum_prod_type, weight, Finset.smul_sum, smul_smul]

theorem mixture_commute (p : PMF ι) (q : PMF κ) (ρ : ι → κ → Density a) :
    (mixture p (fun i => mixture q (ρ i))).matrix =
      (mixture q (fun j => mixture p (fun i => ρ i j))).matrix := by
  simp only [mixture, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end
end Foundation.Quantum.Density
