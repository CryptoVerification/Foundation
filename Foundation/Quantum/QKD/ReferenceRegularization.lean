import Foundation.Quantum.QKD.DominatedCollision
import Mathlib.Analysis.SpecificLimits.Basic

/-! Remove faithfulness from the finite domination-based hash bound by adding
a positive scalar identity to the reference, normalizing it, and taking a
scalar error limit. No inverse of a singular matrix is treated as an inverse.
This is an independent finite-dimensional proof, not a construction of the
support-restricted inverse or of infinite-dimensional trace-class limits. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

def referenceScale (e : Space) (δ : ℝ) : ℝ := 1 + δ * Fintype.card e.Basis

theorem referenceScale_pos (δ : ℝ) (hδ : 0 ≤ δ) : 0 < referenceScale e δ := by
  unfold referenceScale
  positivity

/-- A normalized positive reference with an actual strictly positive identity perturbation. -/
def regularizeReference (τ : Density e) (δ : ℝ) (hδ : 0 < δ) : Density e where
  matrix := ((1/referenceScale e δ : ℝ):ℂ) • (τ.matrix + (δ:ℂ) • 1)
  positive := (τ.positive.add (Matrix.PosSemidef.one.smul
    (Complex.nonneg_iff.mpr ⟨hδ.le,by simp⟩))).smul
      (Complex.nonneg_iff.mpr ⟨(one_div_pos.mpr (referenceScale_pos δ hδ.le)).le,by simp⟩)
  normalized := by
    simp only [Matrix.trace_smul, Matrix.trace_add, τ.normalized, Matrix.trace_one, smul_eq_mul]
    have hs : referenceScale e δ ≠ 0 := ne_of_gt (referenceScale_pos δ hδ.le)
    have hr : (1/referenceScale e δ : ℝ) * (1+δ*Fintype.card e.Basis) = 1 := by
      change (1/referenceScale e δ) * referenceScale e δ = 1
      field_simp
    exact_mod_cast hr

theorem regularizeReference_isUnit (τ : Density e) (δ : ℝ) (hδ : 0 < δ) :
    IsUnit (regularizeReference τ δ hδ).matrix := by
  apply Matrix.PosDef.isUnit
  exact (Matrix.PosDef.posSemidef_add τ.positive (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hδ))).smul
    (Complex.zero_lt_real.mpr (one_div_pos.mpr (referenceScale_pos δ hδ.le)))

/-- The normalization changes the coefficient explicitly; the additional
positive identity term is proved, rather than postulating domination. -/
theorem regularizeReference_scaled (τ : Density e) (δ : ℝ) (hδ : 0 < δ) (q : ℝ) :
    ((q*referenceScale e δ : ℝ):ℂ) • (regularizeReference τ δ hδ).matrix =
      (q:ℂ) • τ.matrix + ((q*δ:ℝ):ℂ) • 1 := by
  have hs : referenceScale e δ ≠ 0 := ne_of_gt (referenceScale_pos δ hδ.le)
  have hc : ((q*referenceScale e δ : ℝ):ℂ) * ((1/referenceScale e δ : ℝ):ℂ) = (q:ℂ) := by
    have hr : q*referenceScale e δ*(1/referenceScale e δ) = q := by field_simp
    exact_mod_cast hr
  change ((q*referenceScale e δ : ℝ):ℂ) • (((1/referenceScale e δ : ℝ):ℂ) • _) = _
  rw [smul_smul, hc, smul_add, smul_smul, Complex.ofReal_mul]

theorem regularizeReference_domination {X : Type} [Fintype X] (ρ : Subnormalized.State X e)
    (τ : Density e) (q : ℝ) (hq : 0 ≤ q) (hdom : Subnormalized.Dominated ρ τ q)
    (δ : ℝ) (hδ : 0 < δ) :
    Subnormalized.Dominated ρ (regularizeReference τ δ hδ) (q*referenceScale e δ) := by
  intro x
  rw [regularizeReference_scaled]
  have hs : (0:ℂ) ≤ ((q*δ:ℝ):ℂ) := Complex.nonneg_iff.mpr ⟨mul_nonneg hq hδ.le,by simp⟩
  have hp := (hdom x).add (Matrix.PosSemidef.one.smul hs)
  convert hp using 1; abel

/-- The same observation bound holds for a possibly singular reference.
Only a scalar continuous error limit is used; the joint real and ideal
operators stay fixed throughout the sequence of faithful references. -/
theorem dominated_published_distance_general {X Y S : Type} [Fintype X] [Fintype Y]
    [Nonempty Y] [DecidableEq Y] [Fintype S]
    (p : PMF S) (h : S → X → Y) (ρ : Subnormalized.State X e)
    (τ : Density e) (q : ℝ) (hq : 0 ≤ q) (hdom : Subnormalized.Dominated ρ τ q)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox (publicMixture p (fun s => hashed ρ.block (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) ρ.block))
        ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*(q*Subnormalized.mass ρ)))) := by
  let error : ℝ → ℝ := fun δ => (1/2:ℝ)*Real.sqrt (Fintype.card Y *
    ((1-1/Fintype.card Y)*(q*referenceScale e δ*Subnormalized.mass ρ)))
  have he : Continuous error := by unfold error referenceScale; fun_prop
  have ht := he.continuousAt.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl : Filter.Tendsto (fun n : Nat => error (1/((n:ℝ)+1))) Filter.atTop
      (nhds ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*(q*Subnormalized.mass ρ))))) := by
    simpa only [Function.comp_def, error, referenceScale, zero_mul, add_zero, mul_one] using ht
  intro E
  apply ge_of_tendsto' hl
  intro n
  have hn : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
  exact dominated_published_distance p h ρ (regularizeReference τ _ hn)
    (regularizeReference_isUnit τ _ hn) _ (regularizeReference_domination ρ τ q hq hdom _ hn) hδ E

end
end Foundation.Quantum.QKD.Collision
