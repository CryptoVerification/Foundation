import Foundation.Quantum.QKD.QuantumErrorSampling
import Foundation.Quantum.Instrument

/-! An actual two-outcome diagonal quantum test retains the quantum state.
Its accepted branch on the sampled ideal state has small error support. This
is a virtual basis test; its equality to BB84's physical phase experiment is
not assumed. -/
namespace Foundation.Quantum.QKD.QuantumErrorTest
noncomputable section
open PureProjection SupportProjection
set_option backward.isDefEq.respectTransparency false
variable {a : Space}

def mask (P : a.Basis → Prop) [DecidablePred P] : Operator a :=
  Matrix.diagonal (fun i => if P i then 1 else 0)

theorem mask_adjoint (P : a.Basis → Prop) [DecidablePred P] : (mask P).conjTranspose = mask P := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : P i <;> simp [mask, Matrix.conjTranspose_apply, hi]
  · simp [mask, Matrix.conjTranspose_apply, hij, Ne.symm hij]

def test (P : a.Basis → Prop) [DecidablePred P] : Instrument a a 2 where
  branch r := Kraus.single (mask (fun i => if r = 0 then P i else ¬ P i))
  complete := by
    simp only [Fin.sum_univ_two, Kraus.single_effect, mask_adjoint]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : P i <;>
        simp [mask, Matrix.diagonal_mul_diagonal, hi]
    · simp [mask, Matrix.diagonal_mul_diagonal, hij]

theorem accepted_operator (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) :
    ((test P).branch 0).apply (rank v v) = rank (keep P v) (keep P v) := by
  change (Kraus.single (mask (fun i => if (0:Fin 2) = 0 then P i else ¬ P i))).apply _ = _
  simp only [Kraus.single_apply, mask_adjoint]
  ext i j
  by_cases hi : P i <;> by_cases hj : P j <;>
    simp [mask, Matrix.diagonal_mul, Matrix.mul_diagonal, rank, Matrix.vecMulVec_apply,
      Pi.star_apply, keep, hi, hj]

variable {I : Type} [DecidableEq I]

/-- Every nonzero accepted amplitude of the constructed ideal vector has
fewer than `bad` errors; this is proved for the actual test's filtered vector. -/
theorem accepted_support (U : Finset I) (bad : Nat) (pattern : a.Basis → Finset I)
    (T : Finset I) (v : a.Basis → ℂ) (fallback : a.Basis)
    (hf : QuantumErrorSampling.good U bad pattern T fallback) (i : a.Basis)
    (hi : keep (fun j => Sampling.undetected (pattern j) T)
      (SupportProjection.vector (QuantumErrorSampling.good U bad pattern T) v fallback) i ≠ 0) :
    (pattern i ∩ U).card < bad := by
  by_cases ht : Sampling.undetected (pattern i) T
  · apply QuantumErrorSampling.accepted_support U bad pattern T v fallback hf i ht
    simpa only [keep, if_pos ht] using hi
  · simp only [keep, if_neg ht, ne_eq, not_true_eq_false] at hi

/-- The accepted branch has no rows at all with a large error pattern,
including every auxiliary coherence coordinate in those rows. -/
theorem accepted_zero_row (U : Finset I) (bad : Nat) (pattern : a.Basis → Finset I)
    (T : Finset I) (v : a.Basis → ℂ) (fallback : a.Basis)
    (hf : QuantumErrorSampling.good U bad pattern T fallback) (i j : a.Basis)
    (hi : bad ≤ (pattern i ∩ U).card) :
    ((test (fun k => Sampling.undetected (pattern k) T)).branch 0).apply
      (SupportProjection.state (QuantumErrorSampling.good U bad pattern T) v fallback).matrix i j = 0 := by
  rw [show (SupportProjection.state _ _ _).matrix = rank
    (SupportProjection.vector (QuantumErrorSampling.good U bad pattern T) v fallback)
    (SupportProjection.vector (QuantumErrorSampling.good U bad pattern T) v fallback) from rfl,
    accepted_operator]
  have hz : keep (fun k => Sampling.undetected (pattern k) T)
      (SupportProjection.vector (QuantumErrorSampling.good U bad pattern T) v fallback) i = 0 := by
    by_contra hn
    have hh := accepted_support U bad pattern T v fallback hf i hn
    omega
  simp only [rank, Matrix.vecMulVec_apply, hz, zero_mul]

end
end Foundation.Quantum.QKD.QuantumErrorTest
