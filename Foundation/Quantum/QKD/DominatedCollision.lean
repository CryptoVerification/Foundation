import Foundation.Quantum.QKD.ReferenceRoot
import Foundation.Quantum.QKD.SubnormalizedGuess

/-! Operator domination bounds the weighted input collision. No distance
conclusion or scalar replacement of quantum cross terms is assumed. The
reference is faithful in this module; singular references remain separate. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

/-- Conjugating the reference by its inverse fourth root gives its square root. -/
theorem inverse_quarter_reference (T : Operator e) (hT : T.PosSemidef) (hunit : IsUnit T) :
    (quarterRoot T)⁻¹ * T * ((quarterRoot T)⁻¹).conjTranspose = quarterRoot T * quarterRoot T := by
  let D := quarterRoot T
  have hd : D.IsHermitian := (quarterRoot_positive T).isHermitian
  have hu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp (quarterRoot_isUnit T hT hunit)
  have ht : T = D*(D*D)*D := by
    have hf := quarterRoot_fourth T hT
    rw [hd.eq] at hf
    simpa only [D, Matrix.mul_assoc] using hf.symm
  change D⁻¹*T*(D⁻¹).conjTranspose = D*D
  rw [Matrix.conjTranspose_nonsing_inv, hd.eq, ht]
  calc
    _ = (D⁻¹*D)*(D*D)*(D*D⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul D hu, Matrix.mul_nonsing_inv D hu]; simp

/-- The weighted square of one dominated positive block is at most q times
its actual trace, without assuming that the block commutes with the reference. -/
theorem dominated_block_collision (τ : Density e) (hτ : IsUnit τ.matrix)
    (B : Operator e) (hB : B.PosSemidef) (q : ℝ) (hdom : (((q:ℂ) • τ.matrix)-B).PosSemidef) :
    (((quarterRoot τ.matrix)⁻¹ * B * ((quarterRoot τ.matrix)⁻¹).conjTranspose) *
      ((quarterRoot τ.matrix)⁻¹ * B * ((quarterRoot τ.matrix)⁻¹).conjTranspose)).trace.re ≤ q * B.trace.re := by
  let D := quarterRoot τ.matrix
  let W := D⁻¹
  let C := W*B*W.conjTranspose
  have hC : C.PosSemidef := hB.mul_mul_conjTranspose_same W
  have hd : D.IsHermitian := (quarterRoot_positive τ.matrix).isHermitian
  have hq := hdom.mul_mul_conjTranspose_same W
  have hwt : W*τ.matrix*W.conjTranspose = D*D := inverse_quarter_reference τ.matrix τ.positive hτ
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hwt] at hq
  change ((q:ℂ) • (D*D) - C).PosSemidef at hq
  have hp := (Complex.nonneg_iff.mp (trace_product_nonneg hC hq)).1
  have hr := inverse_quarter_reconstruct τ.matrix B τ.positive hτ
  change B = D.conjTranspose*C*D at hr
  rw [hd.eq] at hr
  have ht : (C*(D*D)).trace = B.trace := by
    calc
      _ = (D*C*D).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (C*D) D
      _ = _ := congrArg Matrix.trace hr.symm
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    ht, Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hp
  change (C*C).trace.re ≤ q*B.trace.re
  linarith

/-- Summing the block inequalities retains the original subnormalized mass. -/
theorem dominated_input_collision {X : Type} [Fintype X]
    (ρ : Subnormalized.State X e) (τ : Density e) (hτ : IsUnit τ.matrix) (q : ℝ)
    (hdom : Subnormalized.Dominated ρ τ q) :
    input (sandwich (quarterRoot τ.matrix)⁻¹ ρ.block) ≤ q * Subnormalized.mass ρ := by
  unfold input pair sandwich
  calc
    _ ≤ ∑ x, q*(ρ.block x).trace.re := Finset.sum_le_sum (fun x _ =>
      dominated_block_collision τ hτ (ρ.block x) (ρ.positive x) q (hdom x))
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Privacy amplification with a fresh published seed, from an operator
inequality on the accepted (possibly zero-mass) input state. -/
theorem dominated_published_distance {X Y S : Type} [Fintype X] [Fintype Y]
    [Nonempty Y] [DecidableEq Y] [Fintype S]
    (p : PMF S) (h : S → X → Y) (ρ : Subnormalized.State X e)
    (τ : Density e) (hτ : IsUnit τ.matrix) (q : ℝ)
    (hdom : Subnormalized.Dominated ρ τ q)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox (publicMixture p (fun s => hashed ρ.block (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) ρ.block))
        ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*(q*Subnormalized.mass ρ)))) :=
  faithful_reference_interpreted p h ρ.block ρ.positive τ hτ _ (dominated_input_collision ρ τ hτ q hdom) hδ

end
end Foundation.Quantum.QKD.Collision
