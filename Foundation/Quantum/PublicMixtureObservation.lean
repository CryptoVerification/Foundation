import Foundation.Quantum.OperatorDistance
import Foundation.Quantum.QKD.GuessPublic

/-! Observation distance with a publicly recorded fresh finite seed. Arbitrary
joint effects are reduced to their seed-diagonal blocks. The seed is retained,
so the observer may choose a different effect after learning its value. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [Fintype S] {a : Space}

/-- A finite classical seed beside an arbitrary family of actual operators. -/
def publicMixture (p : PMF S) (A : S → Operator a) :
    Operator (QKD.Guessing.publicSpace S a) :=
  ∑ s, ((p s).toReal : ℂ) • Matrix.kronecker
    (basisDensity (.register (Fintype.card S)) (Fintype.equivFin S s)).matrix (A s)

theorem publicMixture_block [DecidableEq S] (p : PMF S) (A : S → Operator a)
    (s t : S) (i j : a.Basis) :
    publicMixture p A (Fintype.equivFin S s,i) (Fintype.equivFin S t,j) =
      if s = t then ((p s).toReal : ℂ) * A s i j else 0 := by
  by_cases h : s = t
  · subst t
    simp [publicMixture, basisDensity, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.diagonal_apply]
  · simp [publicMixture, basisDensity, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.diagonal_apply, h]

theorem publicMixture_positive (p : PMF S) (A : S → Operator a) (hA : ∀ s, (A s).PosSemidef) :
    (publicMixture p A).PosSemidef :=
  Matrix.posSemidef_sum _ (fun s _ => ((basisDensity _ _).positive.kronecker (hA s)).smul
    (Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, by simp⟩))

theorem publicMixture_trace (p : PMF S) (A : S → Operator a) :
    (publicMixture p A).trace = ∑ s, ((p s).toReal : ℂ) * (A s).trace := by
  unfold publicMixture Matrix.kronecker
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker,
    (basisDensity _ _).normalized, one_mul, smul_eq_mul]

/-- Reading a principal public block of an arbitrary joint binary effect
again gives a binary effect, including the upper bound by the identity. -/
def Effect.readPublic (E : Effect (QKD.Guessing.publicSpace S a)) (s : S) : Effect a where
  matrix := E.matrix.submatrix (fun i => (Fintype.equivFin S s,i))
    (fun i => (Fintype.equivFin S s,i))
  positive := E.positive.submatrix _
  complement_positive := by
    have h := E.complement_positive.submatrix (fun i => (Fintype.equivFin S s,i))
    have he : (1 - E.matrix).submatrix (fun i => (Fintype.equivFin S s,i))
        (fun i => (Fintype.equivFin S s,i)) = 1 -
          E.matrix.submatrix (fun i => (Fintype.equivFin S s,i)) (fun i => (Fintype.equivFin S s,i)) := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    rwa [he] at h

theorem publicMixture_observation (p : PMF S) (A : S → Operator a)
    (E : Effect (QKD.Guessing.publicSpace S a)) :
    (E.matrix * publicMixture p A).trace.re =
      ∑ s, (p s).toReal * ((E.readPublic s).matrix * A s).trace.re := by
  unfold publicMixture
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro s _
  rw [QKD.Guessing.trace_classical_block]
  rfl

/-- All joint observations, even depending on the published seed, satisfy
the probability-weighted sum of the individual observation bounds. -/
theorem publicMixture_approx (p : PMF S) (A B : S → Operator a) (ε : S → ℝ)
    (h : ∀ s, OperatorApprox (A s) (B s) (ε s)) :
    OperatorApprox (publicMixture p A) (publicMixture p B) (∑ s, (p s).toReal * ε s) := by
  intro E
  rw [publicMixture_observation, publicMixture_observation, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ s, |(p s).toReal * (((E.readPublic s).matrix * A s).trace.re -
        ((E.readPublic s).matrix * B s).trace.re)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, (p s).toReal * |((E.readPublic s).matrix * A s).trace.re -
        ((E.readPublic s).matrix * B s).trace.re| := by
      simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s (E.readPublic s)) ENNReal.toReal_nonneg)

/-- Concavity of the square root for the actual finite seed distribution. -/
theorem probability_sqrt_bound (p : PMF S) (q : S → ℝ) (hq : ∀ s, 0 ≤ q s) :
    (∑ s, (p s).toReal * Real.sqrt (q s)) ≤ Real.sqrt (∑ s, (p s).toReal * q s) := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (f := fun s => (p s).toReal) (g := fun s => (p s).toReal * q s)
    (fun _ => ENNReal.toReal_nonneg) (fun s => mul_nonneg ENNReal.toReal_nonneg (hq s))
  simp_rw [Real.sqrt_mul ENNReal.toReal_nonneg, ← mul_assoc, Real.mul_self_sqrt ENNReal.toReal_nonneg] at h
  simpa only [Density.probability_weights, Real.sqrt_one, one_mul] using h

/-- A shared reconstruction cost combines with the average weighted square,
rather than a worst seed. The seed is part of the observed joint operator. -/
theorem publicMixture_of_factors (p : PMF S) (A B C : S → Operator a) (D : Operator a)
    (hC : ∀ s, (C s).IsHermitian) (hrec : ∀ s, A s-B s = D.conjTranspose*C s*D)
    (htrace : ∀ s, (A s).trace = (B s).trace) :
    OperatorApprox (publicMixture p A) (publicMixture p B) ((1/2:ℝ) * Real.sqrt
      (((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re *
        ∑ s, (p s).toReal * (C s*C s).trace.re)) := by
  let cost := ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re
  have hcost : 0 ≤ cost := trace_square_nonneg _ (Matrix.posSemidef_self_mul_conjTranspose D).isHermitian
  have hq (s : S) : 0 ≤ cost*(C s*C s).trace.re := mul_nonneg hcost (trace_square_nonneg _ (hC s))
  have hb := publicMixture_approx p A B (fun s => (1/2:ℝ)*Real.sqrt (cost*(C s*C s).trace.re))
    (fun s => OperatorApprox.of_factor _ _ _ _ (hC s) (hrec s) (htrace s))
  apply hb.weaken
  have hs := probability_sqrt_bound p (fun s => cost*(C s*C s).trace.re) hq
  have he : (∑ s, (p s).toReal * (cost*(C s*C s).trace.re)) =
      cost * ∑ s, (p s).toReal * (C s*C s).trace.re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he] at hs
  calc
    _ = (1/2:ℝ) * ∑ s, (p s).toReal * Real.sqrt (cost*(C s*C s).trace.re) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

end
end Foundation.Quantum
