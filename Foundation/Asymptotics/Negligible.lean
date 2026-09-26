import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.Filter.AtTopBot.Basic
import Foundation.Asymptotics.PolynomiallyBounded

open scoped ENNReal
open Filter

/-- The inverse of a positive monomial in `n + 1`. -/
noncomputable def invPoly (k n : Nat) : ℝ≥0∞ :=
  (((n + 1 : Nat) : ℝ≥0∞) ^ k)⁻¹

theorem invPoly_zero (n : Nat) : invPoly 0 n = 1 := by
  simp [invPoly]

/-- An advantage bound is negligible when it is eventually below every
positive inverse-polynomial exponent. No monotonicity or probability-range
condition is imposed on the function. -/
def Negligible (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ k : Nat, ∀ᶠ n in atTop, ε n ≤ invPoly (k + 1) n

namespace Negligible

theorem zero : Negligible (fun _ => 0) := by
  intro k
  exact Filter.Eventually.of_forall (fun n => by exact zero_le)

/-- Eventual upper bounds suffice because negligibility ignores finite prefixes. -/
theorem mono_eventually {ε δ : Nat → ℝ≥0∞}
    (hεδ : ∀ᶠ n in atTop, ε n ≤ δ n) (hδ : Negligible δ) :
    Negligible ε := by
  intro k
  filter_upwards [hεδ, hδ k] with n hle hbound
  exact hle.trans hbound

theorem mono {ε δ : Nat → ℝ≥0∞}
    (hεδ : ∀ n, ε n ≤ δ n) (hδ : Negligible δ) :
    Negligible ε := by
  apply mono_eventually _ hδ
  exact Filter.Eventually.of_forall hεδ

/-- Changing finitely many values does not change negligibility. -/
theorem congr {ε δ : Nat → ℝ≥0∞}
    (h : ε =ᶠ[atTop] δ) : Negligible ε ↔ Negligible δ := by
  constructor
  · intro hε
    apply mono_eventually _ hε
    exact h.mono (fun _ heq => le_of_eq heq.symm)
  · intro hδ
    apply mono_eventually _ hδ
    exact h.mono (fun _ heq => le_of_eq heq)

/-- One extra inverse-power exponent absorbs the factor two for `n ≥ 1`. -/
private theorem add_invPoly_le (k n : Nat) (hn : 1 ≤ n) :
    invPoly (k + 2) n + invPoly (k + 2) n ≤ invPoly (k + 1) n := by
  let t : ℝ≥0∞ := ((n + 1 : Nat) : ℝ≥0∞)
  have ht : (2 : ℝ≥0∞) ≤ t := by
    dsimp [t]
    exact_mod_cast Nat.succ_le_succ hn
  have ht0 : t ≠ 0 := by
    dsimp [t]
    simp
  have htTop : t ≠ ∞ := by
    dsimp [t]
    exact ENNReal.natCast_ne_top _
  have hfactor : (2 : ℝ≥0∞) * t⁻¹ ≤ 1 := by
    calc
      2 * t⁻¹ ≤ t * t⁻¹ := mul_le_mul_left ht _
      _ = 1 := ENNReal.mul_inv_cancel ht0 htTop
  have hpow : invPoly (k + 2) n = invPoly (k + 1) n * t⁻¹ := by
    change (t ^ (k + 2))⁻¹ = (t ^ (k + 1))⁻¹ * t⁻¹
    rw [show k + 2 = (k + 1) + 1 by omega, ENNReal.inv_pow,
      ENNReal.inv_pow, pow_succ]
  calc
    invPoly (k + 2) n + invPoly (k + 2) n =
        2 * invPoly (k + 2) n := by rw [two_mul]
    _ = (2 * t⁻¹) * invPoly (k + 1) n := by rw [hpow]; ac_rfl
    _ ≤ 1 * invPoly (k + 1) n := mul_le_mul_left hfactor _
    _ = invPoly (k + 1) n := one_mul _

theorem add {ε δ : Nat → ℝ≥0∞}
    (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (fun n => ε n + δ n) := by
  intro k
  filter_upwards [hε (k + 1), hδ (k + 1),
    (eventually_ge_atTop 1)] with n hεn hδn hn
  calc
    ε n + δ n ≤ invPoly (k + 2) n + invPoly (k + 2) n :=
      add_le_add hεn hδn
    _ ≤ invPoly (k + 1) n := add_invPoly_le k n hn

/-- A polynomially bounded multiplicative loss preserves negligibility.
This is the scalar estimate used for polynomial-loss reductions. -/
theorem mul_polynomial {ε : Nat → ℝ≥0∞} {p : Nat → Nat}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0∞) * ε n) := by
  obtain ⟨c, k, hp⟩ := hp
  intro j
  filter_upwards [hp, hε (j + k + 1), eventually_ge_atTop c]
    with n hpn hεn hcn
  let t : ℝ≥0∞ := ((n + 1 : Nat) : ℝ≥0∞)
  have ht0 : t ≠ 0 := by
    dsimp [t]
    simp
  have htTop : t ≠ ∞ := by
    dsimp [t]
    exact ENNReal.natCast_ne_top _
  have hpn' : p n ≤ (n + 1) ^ (k + 1) := by
    calc
      p n ≤ c * (n + 1) ^ k := hpn
      _ ≤ (n + 1) * (n + 1) ^ k := by
        apply Nat.mul_le_mul_right
        omega
      _ = (n + 1) ^ (k + 1) := by rw [pow_succ]; ac_rfl
  have hcast : (p n : ℝ≥0∞) ≤ t ^ (k + 1) := by
    dsimp [t]
    exact_mod_cast hpn'
  have hεn' : ε n ≤ invPoly (j + k + 2) n := by
    simpa [Nat.add_assoc] using hεn
  have hcancel : t ^ (k + 1) * invPoly (j + k + 2) n =
      invPoly (j + 1) n := by
    change t ^ (k + 1) * (t ^ (j + k + 2))⁻¹ = (t ^ (j + 1))⁻¹
    have hfactor : (t ^ (j + k + 2))⁻¹ =
        (t⁻¹) ^ (k + 1) * (t⁻¹) ^ (j + 1) := by
      rw [ENNReal.inv_pow, show j + k + 2 = (k + 1) + (j + 1) by omega]
      exact pow_add _ _ _
    rw [hfactor]
    calc
      t ^ (k + 1) * (t⁻¹ ^ (k + 1) * t⁻¹ ^ (j + 1)) =
          (t * t⁻¹) ^ (k + 1) * t⁻¹ ^ (j + 1) := by rw [mul_pow]; ac_rfl
      _ = (t ^ (j + 1))⁻¹ := by
        rw [ENNReal.mul_inv_cancel ht0 htTop, one_pow, one_mul, ENNReal.inv_pow]
  calc
    (p n : ℝ≥0∞) * ε n ≤ t ^ (k + 1) * invPoly (j + k + 2) n :=
      mul_le_mul hcast hεn' zero_le zero_le
    _ = invPoly (j + 1) n := hcancel

end Negligible
