import Foundation.Constructions.ElGamal.Concrete
import Foundation.Crypto.Semantics.Security.Asymptotic

namespace ElGamal

open Foundation.Probability
open scoped ENNReal

/-- Recover both exponents through the explicit bijection and check the DH
relation. This mathematical adversary has no efficiency witness. In a finite
cyclic representation its inverse can be found by exhaustive search; here
the inverse is supplied by `FiniteAlgebra.powerEquiv`. -/
noncomputable def unrestrictedDDHAdversary (params : DDHParameters)
    (L : FiniteAlgebra params) : DDHAdversary ProbComp params := by
  classical
  exact { distinguish := fun X Y Z => PMF.pure (decide
    (params.power params.generator
      (params.mulScalar (L.powerEquiv.symm X) (L.powerEquiv.symm Y)) = Z)) }

private theorem recover_power (params : DDHParameters) (L : FiniteAlgebra params)
    (x : params.Scalar) :
    L.powerEquiv.symm (params.power params.generator x) = x := by
  rw [← L.powerEquiv_apply]
  exact L.powerEquiv.symm_apply_apply x

theorem unrestrictedDDH_real (params : DDHParameters) (L : FiniteAlgebra params) :
    ddhRealGame params L.sampling (unrestrictedDDHAdversary params L) =
      PMF.pure true := by
  simp [ddhRealGame, unrestrictedDDHAdversary, recover_power, PMF.bind_const]

private theorem uniform_equality_probability {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α]
    (a : α) :
    eventProb ((PMF.uniformOfFintype α).bind
      (fun z => PMF.pure (decide (a = z)))) (· = true) =
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  simp [eventProb]

/-- Under the supplied finite uniform scalar sampler and generator-power
bijection, the random triple satisfies the DH relation with probability
`1 / card Scalar`. No group or sampling assumption is implicit. -/
theorem unrestrictedDDH_random (params : DDHParameters) (L : FiniteAlgebra params) :
    eventProb (ddhRandomGame params L.sampling (unrestrictedDDHAdversary params L))
      (· = true) = (@Fintype.card params.Scalar L.sampling.scalarFintype : ℝ≥0∞)⁻¹ := by
  classical
  let _ := L.sampling.scalarFintype
  let _ := L.sampling.scalarNonempty
  have hPower (a z : params.Scalar) :
      params.power params.generator a = params.power params.generator z ↔ a = z := by
    rw [← L.powerEquiv_apply, ← L.powerEquiv_apply]
    exact L.powerEquiv.injective.eq_iff
  simp only [ddhRandomGame, unrestrictedDDHAdversary, recover_power, hPower]
  unfold eventProb
  simp only [PMF.toOuterMeasure_bind_apply]
  have hInner (a : params.Scalar) :
      ∑' z, L.sampling.sampleScalar z *
        (PMF.pure (decide (a = z))).toOuterMeasure {b | b = true} =
        (Fintype.card params.Scalar : ℝ≥0∞)⁻¹ := by
    simpa only [eventProb, PMF.toOuterMeasure_bind_apply, DDHFiniteSampling.sampleScalar,
      uniform] using uniform_equality_probability a
  simp_rw [hInner]
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem unrestrictedDDH_advantage (params : DDHParameters) (L : FiniteAlgebra params) :
    ddhAdvantage params L.sampling (unrestrictedDDHAdversary params L) =
      1 - (@Fintype.card params.Scalar L.sampling.scalarFintype : ℝ≥0∞)⁻¹ := by
  rw [ddhAdvantage, unrestrictedDDH_real, unrestrictedDDH_random]
  have hle : (@Fintype.card params.Scalar L.sampling.scalarFintype : ℝ≥0∞)⁻¹ ≤ 1 := by
    let _ := L.sampling.scalarFintype
    let _ := L.sampling.scalarNonempty
    have hCard : (1 : ℝ≥0∞) ≤ (Fintype.card params.Scalar : ℝ≥0∞) := by
      exact_mod_cast Fintype.card_pos (α := params.Scalar)
    simpa using ENNReal.inv_le_inv.mpr hCard
  simp [eventProb, probabilityGap, tsub_eq_zero_of_le hle]

/-- For a family of these finite experiments with at least two scalars at
every parameter, unrestricted DDH security is false. The sampler agreement,
generator-power bijection, and cardinality hypotheses are explicit. This
does not contradict security against a restricted machine-PPT class. -/
theorem not_secureDDH_all
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params))
    (F : Nat → DDHParameters) (L : ∀ n, FiniteAlgebra (F n))
    (hSampling : ∀ n, sampling n (F n) = some (L n).sampling)
    (hCard : ∀ n, 2 ≤ @Fintype.card (F n).Scalar (L n).sampling.scalarFintype) :
    ¬ SecureOnWithin (DDH ProbComp (concreteDDHSemantics sampling))
      (AdversaryClass.all _) F := by
  intro hSecure
  let A : AdversaryFamily (DDH ProbComp (concreteDDHSemantics sampling)) F :=
    fun n => unrestrictedDDHAdversary (F n) (L n)
  have hNeg := hSecure A trivial
  have hLower (n : Nat) : (2 : ℝ≥0∞)⁻¹ ≤
      advantageProfile (DDH ProbComp (concreteDDHSemantics sampling)) F A n := by
    change (2 : ℝ≥0∞)⁻¹ ≤ (concreteDDHSemantics sampling).advantage n (F n)
      (unrestrictedDDHAdversary (F n) (L n))
    simp only [concreteDDHSemantics, hSampling, unrestrictedDDH_advantage]
    have hCast : (2 : ℝ≥0∞) ≤
        (@Fintype.card (F n).Scalar (L n).sampling.scalarFintype : ℝ≥0∞) := by
      exact_mod_cast hCard n
    calc
      (2 : ℝ≥0∞)⁻¹ = 1 - (2 : ℝ≥0∞)⁻¹ := by norm_num
      _ ≤ _ := tsub_le_tsub_left (ENNReal.inv_le_inv.mpr hCast) 1
  obtain ⟨n, hAdv, hn⟩ := ((hNeg 0).and (Filter.eventually_ge_atTop 2)).exists
  have hlt : invPoly (0 + 1) n < (2 : ℝ≥0∞)⁻¹ := by
    change (((n + 1 : Nat) : ℝ≥0∞) ^ 1)⁻¹ < (2 : ℝ≥0∞)⁻¹
    rw [pow_one, ENNReal.inv_lt_inv]
    exact_mod_cast (show 2 < n + 1 by omega)
  exact (not_le_of_gt hlt) ((hLower n).trans hAdv)

end ElGamal
