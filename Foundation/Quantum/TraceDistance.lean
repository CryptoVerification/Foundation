import Foundation.Quantum.StateDistance
import Mathlib.Analysis.Matrix.Spectrum

/-! Finite-dimensional trace distance in the standard half-trace-norm
convention. For Hermitian differences the trace norm is the sum of absolute
eigenvalues. The positive spectral projector attains the operational bound. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

namespace HermitianTrace
variable {a : Space} {A : Operator a}

def spectralMatrix (h : A.IsHermitian) (f : a.Basis → ℝ) : Operator a :=
  (h.eigenvectorUnitary : Operator a) * Matrix.diagonal (fun i => (f i : ℂ)) *
    (h.eigenvectorUnitary : Operator a).conjTranspose

theorem spectral_positive (h : A.IsHermitian) (f : a.Basis → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (spectralMatrix h f).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.PosSemidef.diagonal (fun i => by simpa using hf i)

theorem spectral_trace (h : A.IsHermitian) (f : a.Basis → ℝ) :
    (spectralMatrix h f).trace.re = ∑ i, f i := by
  unfold spectralMatrix
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]

theorem spectral_sub (h : A.IsHermitian) (f g : a.Basis → ℝ) :
    spectralMatrix h (fun i => f i - g i) = spectralMatrix h f - spectralMatrix h g := by
  unfold spectralMatrix
  have hd : Matrix.diagonal (fun i => ((f i - g i : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (f i : ℂ)) - Matrix.diagonal (fun i => (g i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul]

theorem spectral_self (h : A.IsHermitian) : spectralMatrix h h.eigenvalues = A := by
  simpa [spectralMatrix, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def] using h.spectral_theorem.symm

def traceNorm (h : A.IsHermitian) : ℝ := ∑ i, |h.eigenvalues i|

def positivePart (h : A.IsHermitian) : Operator a :=
  spectralMatrix h (fun i => max (h.eigenvalues i) 0)

def negativePart (h : A.IsHermitian) : Operator a :=
  spectralMatrix h (fun i => max (-h.eigenvalues i) 0)

theorem parts_difference (h : A.IsHermitian) : positivePart h - negativePart h = A := by
  rw [positivePart, negativePart, ← spectral_sub]
  have he : (fun i => max (h.eigenvalues i) 0 - max (-h.eigenvalues i) 0) = h.eigenvalues := by
    funext i
    rcases le_total 0 (h.eigenvalues i) with hi | hi
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
  rw [he, spectral_self]

theorem parts_trace_sum (h : A.IsHermitian) :
    (positivePart h).trace.re + (negativePart h).trace.re = traceNorm h := by
  rw [positivePart, negativePart, spectral_trace, spectral_trace, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total 0 (h.eigenvalues i) with hi | hi
  · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
  · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), abs_of_nonpos hi]

theorem positive_trace_half (h : A.IsHermitian) (ht : A.trace = 0) :
    (positivePart h).trace.re = traceNorm h / 2 := by
  have hd := congrArg (fun M : Operator a => M.trace.re) (parts_difference h)
  simp only [Matrix.trace_sub, Complex.sub_re, ht, Complex.zero_re] at hd
  have hs := parts_trace_sum h
  linarith

theorem effect_trace_bounds (E : Effect a) {P : Operator a} (hP : P.PosSemidef) :
    0 ≤ (E.matrix * P).trace.re ∧ (E.matrix * P).trace.re ≤ P.trace.re := by
  have hl := (Complex.nonneg_iff.mp (trace_product_nonneg E.positive hP)).1
  have hu := (Complex.nonneg_iff.mp (trace_product_nonneg E.complement_positive hP)).1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hu
  exact ⟨hl, by linarith⟩

theorem effect_bound (h : A.IsHermitian) (ht : A.trace = 0) (E : Effect a) :
    |(E.matrix * A).trace.re| ≤ traceNorm h / 2 := by
  have hp := effect_trace_bounds E
    (spectral_positive h (fun i => max (h.eigenvalues i) 0) (fun _ => le_max_right _ _))
  have hn := effect_trace_bounds E
    (spectral_positive h (fun i => max (-h.eigenvalues i) 0) (fun _ => le_max_right _ _))
  change 0 ≤ (E.matrix * positivePart h).trace.re ∧
    (E.matrix * positivePart h).trace.re ≤ (positivePart h).trace.re at hp
  change 0 ≤ (E.matrix * negativePart h).trace.re ∧
    (E.matrix * negativePart h).trace.re ≤ (negativePart h).trace.re at hn
  have he := positive_trace_half h ht
  have hd := congrArg (fun M : Operator a => M.trace.re) (parts_difference h)
  simp only [Matrix.trace_sub, Complex.sub_re, ht, Complex.zero_re] at hd
  conv_lhs => rw [← parts_difference h, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem spectral_one (h : A.IsHermitian) : spectralMatrix h (fun _ => 1) = 1 := by
  simp [spectralMatrix, ← Matrix.star_eq_conjTranspose]

theorem spectral_product_trace (h : A.IsHermitian) (f g : a.Basis → ℝ) :
    (spectralMatrix h f * spectralMatrix h g).trace.re = ∑ i, f i * g i := by
  unfold spectralMatrix
  simp only [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (h.eigenvectorUnitary : Operator a))]
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
    Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

def positiveEffect (h : A.IsHermitian) : Effect a where
  matrix := spectralMatrix h (fun i => if 0 < h.eigenvalues i then 1 else 0)
  positive := spectral_positive h _ (fun i => by split_ifs <;> norm_num)
  complement_positive := by
    rw [← spectral_one h, ← spectral_sub]
    apply spectral_positive
    intro i
    split_ifs <;> norm_num

theorem positiveEffect_attains (h : A.IsHermitian) (ht : A.trace = 0) :
    ((positiveEffect h).matrix * A).trace.re = traceNorm h / 2 := by
  have he : ((positiveEffect h).matrix * A).trace.re = (positivePart h).trace.re := by
    have hr := congrArg (fun B : Operator a => ((positiveEffect h).matrix * B).trace.re)
      (spectral_self h).symm
    rw [hr]
    change (spectralMatrix h (fun i => if 0 < h.eigenvalues i then 1 else 0) *
      spectralMatrix h h.eigenvalues).trace.re = _
    rw [spectral_product_trace, positivePart, spectral_trace]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < h.eigenvalues i
    · simp [hi, max_eq_left (le_of_lt hi)]
    · simp [hi, max_eq_right (le_of_not_gt hi)]
  exact he.trans (positive_trace_half h ht)

end HermitianTrace

namespace Density
variable {a : Space}

theorem differenceHermitian (ρ σ : Density a) : (ρ.matrix - σ.matrix).IsHermitian :=
  ρ.positive.isHermitian.sub σ.positive.isHermitian

/-- Standard trace distance: half the sum of absolute eigenvalues of the
Hermitian difference, equivalently half its Schatten 1-norm. -/
def traceDistance (ρ σ : Density a) : ℝ :=
  HermitianTrace.traceNorm (differenceHermitian ρ σ) / 2

theorem difference_trace_zero (ρ σ : Density a) : (ρ.matrix - σ.matrix).trace = 0 := by
  rw [Matrix.trace_sub, ρ.normalized, σ.normalized, sub_self]

theorem effect_le_traceDistance (ρ σ : Density a) (E : Effect a) :
    |E.probability ρ - E.probability σ| ≤ traceDistance ρ σ := by
  have h := HermitianTrace.effect_bound (differenceHermitian ρ σ) (difference_trace_zero ρ σ) E
  simpa [Effect.probability, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, traceDistance] using h

/-- Helstrom's optimal binary test, with the standard factor of one half. -/
theorem exists_effect_attaining_traceDistance (ρ σ : Density a) :
    ∃ E : Effect a, E.probability ρ - E.probability σ = traceDistance ρ σ := by
  refine ⟨HermitianTrace.positiveEffect (differenceHermitian ρ σ), ?_⟩
  have h := HermitianTrace.positiveEffect_attains (differenceHermitian ρ σ) (difference_trace_zero ρ σ)
  simpa [Effect.probability, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, traceDistance] using h

theorem stateApprox_iff_traceDistance_le (ρ σ : Density a) (ε : ℝ) :
    StateApprox ρ σ ε ↔ traceDistance ρ σ ≤ ε := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ := exists_effect_attaining_traceDistance ρ σ
    have hn : 0 ≤ traceDistance ρ σ := by
      unfold traceDistance HermitianTrace.traceNorm
      positivity
    simpa only [hE, abs_of_nonneg hn] using h E
  · intro h E
    exact (effect_le_traceDistance ρ σ E).trans h

theorem traceDistance_self (ρ : Density a) : traceDistance ρ ρ = 0 := by
  have hu := (stateApprox_iff_traceDistance_le ρ ρ 0).mp (StateApprox.refl ρ)
  have hl : 0 ≤ traceDistance ρ ρ := by unfold traceDistance HermitianTrace.traceNorm; positivity
  exact le_antisymm hu hl

theorem traceDistance_le_one (ρ σ : Density a) : traceDistance ρ σ ≤ 1 := by
  obtain ⟨E, hE⟩ := exists_effect_attaining_traceDistance ρ σ
  have hu := E.probability_le_one ρ
  have hl := E.probability_nonneg σ
  linarith

end Density
end
end Foundation.Quantum
