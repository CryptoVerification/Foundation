import Foundation.Quantum.QKD.PairwiseAliceState

/-! The complementary-support certificate survives the error-dependent
bijection to Alice's actual full key, with no factor for the public error record.
Test-key disclosure and removal remain separate from this coordinate change. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

theorem acceptedAlice_dominated {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    Subnormalized.Dominated (acceptedAlice v hv k gap minKey tolerance c)
      (reference v hv k gap c) (bound k gap minKey tolerance c) := by
  intro x
  have hp (r : (qubits n).Basis) :
      ((bound k gap minKey tolerance c : ℂ) • covariance v hv k gap c r -
        (if BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) then
          keyBlock v hv k gap c r (alice n (PairwiseRecordedSampling.basis c) r x) else 0)).PosSemidef := by
    split_ifs with hr
    · exact accepted_key_dominated v hv k gap minKey tolerance c r _ hr
    · rw [sub_zero]
      exact (Matrix.posSemidef_sum _ (fun w _ => CoherentSupport.outer_positive _)).smul
        (Complex.nonneg_iff.mpr ⟨bound_nonneg _ _ _ _ _,by simp⟩)
  have h : (∑ r : (qubits n).Basis, Matrix.kronecker
      (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).matrix
      ((bound k gap minKey tolerance c : ℂ) • covariance v hv k gap c r -
        (if BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) then
          keyBlock v hv k gap c r (alice n (PairwiseRecordedSampling.basis c) r x) else 0))).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun r _ =>
      (basisDensity (.register (Fintype.card (qubits n).Basis))
        (Fintype.equivFin (qubits n).Basis r)).positive.kronecker (hp r))
  convert h using 1
  ext ⟨i,u⟩ ⟨j,w⟩
  simp only [reference_eq, acceptedAlice_block, Matrix.sum_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r) <;>
    simp only [hr, ite_true, ite_false, Matrix.zero_apply] <;> ring

theorem alicePrivacy {n : Nat} {e : Space} {Y S : Type}
    [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (p : PMF S) (h : S → (qubits n).Basis → Y)
    (hc : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    (PrivacyAmplificationLogic.model p h
      (fun _ => acceptedAlice v hv k gap minKey tolerance c)
      (fun _ => reference v hv k gap c) hc).Carrier
      (.distance 0 ((1/2:ℝ)*Real.sqrt (Fintype.card Y *
        ((1-1/Fintype.card Y)*(bound k gap minKey tolerance c*1))))) := by
  apply PrivacyAmplificationLogic.sound p h _ _ hc
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0
      (bound k gap minKey tolerance c) 1 _ (bound_nonneg _ _ _ _ _) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact acceptedAlice_dominated v hv k gap minKey tolerance c
  · have hi1 : i = 1 := by omega
    subst i
    exact (acceptedAlice v hv k gap minKey tolerance c).bounded

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
