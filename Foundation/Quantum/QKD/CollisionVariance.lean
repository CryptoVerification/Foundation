import Foundation.Quantum.QKD.WeightedCollision

/-! Exact centered collision identities. The uniform comparator has the same
quantum marginal as the hashed state. Neither normalization nor commutation of
the conditional quantum blocks is assumed. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {e : Space}

theorem grouped_marginal [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    (∑ y, grouped B h y) = ∑ x, B x := by
  unfold grouped
  rw [Finset.sum_comm]
  simp

/-- Algebraic centering identity for one quantum output block. -/
theorem trace_center (A M : Operator e) (q : ℝ) :
    ((A - (q:ℂ) • M) * (A - (q:ℂ) • M)).trace.re =
      (A*A).trace.re - q*(A*M).trace.re - q*(M*A).trace.re + q^2*(M*M).trace.re := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem center_sum (A : Y → Operator e) (q : ℝ) :
    (∑ y, ((A y - (q:ℂ) • ∑ z, A z) * (A y - (q:ℂ) • ∑ z, A z)).trace.re) =
      (∑ y, (A y * A y).trace.re) - 2*q*((∑ y, A y)*(∑ y, A y)).trace.re +
        Fintype.card Y * q^2 * ((∑ y, A y)*(∑ y, A y)).trace.re := by
  have hleft : (∑ y, (A y * (∑ z, A z)).trace.re) = ((∑ y, A y)*(∑ y, A y)).trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul]
  have hright : (∑ y, ((∑ z, A z) * A y).trace.re) = ((∑ y, A y)*(∑ y, A y)).trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum]
  simp_rw [trace_center]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, hleft, hright, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring

/-- Center each output at the uniform distribution tensored with the exact marginal. -/
def deviation [DecidableEq Y] (B : X → Operator e) (h : X → Y) (y : Y) : Operator e :=
  grouped B h y - ((1 / (Fintype.card Y : ℝ) : ℝ):ℂ) • (∑ x, B x)

theorem variance_identity [Nonempty Y] [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    (∑ y, (deviation B h y * deviation B h y).trace.re) =
      (∑ y, (grouped B h y * grouped B h y).trace.re) - (1 / Fintype.card Y) * total B := by
  have hc : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs := center_sum (grouped B h) (1 / Fintype.card Y)
  rw [grouped_marginal] at hs
  unfold deviation total
  rw [hs]
  field_simp
  ring

def variance [DecidableEq Y] (p : PMF S) (h : S → X → Y) (B : X → Operator e) : ℝ :=
  ∑ s, (p s).toReal * ∑ y, (deviation B (h s) y * deviation B (h s) y).trace.re

theorem variance_expansion [Nonempty Y] [DecidableEq Y] (p : PMF S) (h : S → X → Y) (B : X → Operator e) :
    variance p h B = output p h B - (1 / Fintype.card Y) * total B := by
  unfold variance output
  simp_rw [variance_identity]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, Density.probability_weights]
  ring

/-- The centered square has nonnegative real trace for positive input blocks. -/
theorem deviation_square_nonneg [DecidableEq Y] (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) (h : X → Y) (y : Y) :
    0 ≤ (deviation B h y * deviation B h y).trace.re := by
  have hg : (grouped B h y).PosSemidef := Matrix.posSemidef_sum _ (fun x _ => by
    by_cases hx : h x = y
    · simpa only [hx, ite_true] using hB x
    · simp only [hx, ite_false]; exact Matrix.PosSemidef.zero)
  have hm := Matrix.posSemidef_sum Finset.univ (fun x _ => hB x)
  have hq : (0:ℂ) ≤ (((1 / (Fintype.card Y : ℝ) : ℝ):ℂ)) := by
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [Complex.ofReal_re]; positivity
    · simp
  have hd : (deviation B h y).IsHermitian := hg.isHermitian.sub (hm.smul hq).isHermitian
  have hp := Matrix.posSemidef_conjTranspose_mul_self (deviation B h y)
  rw [hd.eq] at hp
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

theorem variance_nonneg [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef) : 0 ≤ variance p h B :=
  Finset.sum_nonneg (fun s _ => mul_nonneg ENNReal.toReal_nonneg
    (Finset.sum_nonneg (fun y _ => deviation_square_nonneg B hB (h s) y)))

theorem variance_sharp_le [Nonempty Y] [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    variance p h B ≤ (1 - 1 / Fintype.card Y) * input B := by
  have hb := output_le p h B hB (1 / Fintype.card Y) hδ
  rw [variance_expansion]
  linarith

/-- The quantum deviation from the uniform comparator has average collision
at most the input collision for a two-universal family. -/
theorem variance_le_input [Nonempty Y] [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    variance p h B ≤ input B := by
  have hbound := output_le p h B hB (1 / Fintype.card Y) hδ
  have hi : 0 ≤ input B := Finset.sum_nonneg (fun x _ => pair_nonneg B hB x x)
  have hc : (0:ℝ) ≤ 1 / Fintype.card Y := by positivity
  rw [variance_expansion]
  nlinarith

end
end Foundation.Quantum.QKD.Collision
