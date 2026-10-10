import Foundation.Quantum.Effects
import Foundation.Crypto.Semantics.Probability.Comp

/-! Finite classical randomness acting on actual quantum states. A mixture is
a density operator, and physical observations and channels commute with it. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

namespace Density
variable {ι : Type*} [Fintype ι] {a b : Space}

theorem probability_weights (p : PMF ι) : ∑ i, (p i).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
  have h : ∑ i, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

/-- Random preparation with an arbitrary finite probability distribution. -/
def mixture (p : PMF ι) (ρ : ι → Density a) : Density a where
  matrix := ∑ i, ((p i).toReal : ℂ) • (ρ i).matrix
  positive := Matrix.posSemidef_sum _ (fun i _ => (ρ i).positive.smul
    (Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, by simp⟩))
  normalized := by
    simp only [Matrix.trace_sum, Matrix.trace_smul, (ρ _).normalized, smul_eq_mul, mul_one]
    norm_cast
    exact probability_weights p

theorem mixture_observation (p : PMF ι) (ρ : ι → Density a) (E : Effect a) :
    E.probability (mixture p ρ) = ∑ i, (p i).toReal * E.probability (ρ i) := by
  simp [Effect.probability, mixture, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.trace_smul, Complex.mul_re]

theorem mixture_channel (p : PMF ι) (ρ : ι → Density a) (C : Channel a b) :
    (C.run (mixture p ρ)).matrix = (mixture p (fun i => C.run (ρ i))).matrix := by
  change C.toKraus.linear (∑ i, ((p i).toReal : ℂ) • (ρ i).matrix) = _
  simp only [map_sum, map_smul, mixture]
  rfl

end Density
end
end Foundation.Quantum
