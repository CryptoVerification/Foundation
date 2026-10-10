import Foundation.Quantum.QKD.PairwisePhaseState
import Foundation.Quantum.QKD.SubnormalizedPublic

/-! A normalized public-error reference and an accepted-branch operator
certificate derived from the actual finite phase support. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

def acceptedSupport {n : Nat} (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) : Nat :=
  (Finset.univ.filter (fun r : (qubits n).Basis =>
    BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r))).sup
      (fun r => (phaseSet k gap c r).card)

def bound {n : Nat} (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) : ℝ :=
  acceptedSupport k gap minKey tolerance c * (1/2:ℝ)^n

theorem bound_nonneg {n : Nat} (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    0 ≤ bound k gap minKey tolerance c := by unfold bound; positivity

def accepted {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :=
  Subnormalized.withPublic (Subnormalized.restrict (Subnormalized.ofCQ (jointState v hv k gap c))
    (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2)))

theorem reference_eq {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    (reference v hv k gap c).matrix =
      ∑ r : (qubits n).Basis, Matrix.kronecker
        (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).matrix
        (covariance v hv k gap c r) := by
  ext ⟨i,u⟩ ⟨j,w⟩
  simp only [reference, Guessing.marginal, Guessing.withPublic, jointState,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.mul_sum]
  simpa only [Matrix.sum_apply] using congrArg (fun τ =>
    (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).matrix i j * τ u w)
    (key_covariance v hv k gap c r)

theorem accepted_key_dominated {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (((bound k gap minKey tolerance c : ℂ) • covariance v hv k gap c r) -
      keyBlock v hv k gap c r z).PosSemidef := by
  have hc : (phaseSet k gap c r).card ≤ acceptedSupport k gap minKey tolerance c :=
    Finset.le_sup (f := fun r => (phaseSet k gap c r).card) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hr)
  have hb : (phaseSet k gap c r).card * (1/2:ℝ)^n ≤ bound k gap minKey tolerance c :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  have hp : (covariance v hv k gap c r).PosSemidef := by
    unfold covariance
    exact Matrix.posSemidef_sum _ (fun w _ => CoherentSupport.outer_positive _)
  have hs := hp.smul (show (0:ℂ) ≤
      ((bound k gap minKey tolerance c - (phaseSet k gap c r).card * (1/2:ℝ)^n : ℝ) : ℂ) from
    Complex.nonneg_iff.mpr ⟨by simpa only [Complex.ofReal_re] using sub_nonneg.mpr hb,rfl⟩)
  have hd := hs.add (key_dominated v hv k gap c r z)
  convert hd using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
  ring

/-- The privacy-amplification input certificate is proved from the same
physical measured approximant, with its detailed error record public. -/
theorem accepted_dominated {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    Subnormalized.Dominated (accepted v hv k gap minKey tolerance c)
      (reference v hv k gap c) (bound k gap minKey tolerance c) := by
  intro z
  have hp (r : (qubits n).Basis) :
      ((bound k gap minKey tolerance c : ℂ) • covariance v hv k gap c r -
        (if BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) then keyBlock v hv k gap c r z else 0)).PosSemidef := by
    split_ifs with hr
    · exact accepted_key_dominated v hv k gap minKey tolerance c r z hr
    · rw [sub_zero]
      exact (Matrix.posSemidef_sum _ (fun w _ => CoherentSupport.outer_positive _)).smul
        (Complex.nonneg_iff.mpr ⟨bound_nonneg _ _ _ _ _,by simp⟩)
  have h : (∑ r : (qubits n).Basis, Matrix.kronecker
      (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).matrix
      ((bound k gap minKey tolerance c : ℂ) • covariance v hv k gap c r -
        (if BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) then keyBlock v hv k gap c r z else 0))).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun r _ =>
    (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).positive.kronecker (hp r))
  convert h using 1
  ext ⟨i,u⟩ ⟨j,w⟩
  simp only [reference_eq, accepted, Subnormalized.withPublic, Subnormalized.restrict,
    Subnormalized.ofCQ, jointState, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) <;>
    simp only [hr, ite_true, ite_false, Matrix.zero_apply] <;> ring

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
