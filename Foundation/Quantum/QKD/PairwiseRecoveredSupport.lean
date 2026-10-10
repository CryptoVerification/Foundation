import Foundation.Quantum.QKD.PairwiseRecordedRecovery

/-! The same recovered normalized ideal state has the required fixed-reference
support. Losing the dilation label does not lose the sampling support bound. -/
namespace Foundation.Quantum.QKD.PairwiseRecovery
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

theorem approximant_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (approximant A M k gap hk).matrix =
      publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (fun c => (PartitionMeasurement.instrument (errorLabel (basis c))).record.toKraus.apply
          ((discard A M).toKraus.apply
            (SupportProjection.state (PairwiseQuantumSampling.good k gap c)
              (PairwiseAttackSampling.vector A M)
              (PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))).matrix)) := by
  change (recover A M).toKraus.apply _ = _
  rw [ideal_eq, recover, RetainedControl.public_apply]
  apply congrArg (publicMixture (PairwiseSampling.distribution _ k hk))
  funext c
  exact record A M (basis c) _

theorem recovered_zero_row {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M)
    (c d : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (r s : Fin (count (BB84SiftedInput.selectedCount M)))
    (i j : (jointSpace (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)).Basis)
    (hi : PairwiseSampling.bad k gap (pairBits i.1) c) :
    (approximant A M k gap hk).matrix (Fintype.equivFin _ c,(r,i))
      (Fintype.equivFin _ d,(s,j)) = 0 := by
  rw [approximant_eq, publicMixture_block]
  by_cases h : c = d
  · subst d
    simp only [ite_true]
    rw [PartitionMeasurement.record_entry]
    split_ifs
    · rcases i with ⟨i,u,x⟩
      rcases j with ⟨j,v,y⟩
      rw [discard, NestedDiscard.apply_entry]
      have hz (t : (krausSpace A).Basis) := PairwiseQuantumSampling.supported
        (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
        k gap c (i,(u,(x,t))) (by simpa only [PairwiseQuantumSampling.good, not_not] using hi)
      have he : (∑ t : (krausSpace A).Basis,
          (SupportProjection.state (PairwiseQuantumSampling.good k gap c)
            (PairwiseAttackSampling.vector A M)
            (PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))).matrix
              (i,(u,(x,t))) (j,(v,(y,t)))) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        simp [SupportProjection.state, PureProjection.pure, rank,
          Matrix.vecMulVec_apply, Pi.star_apply, hz t]
      rw [he, mul_zero]
    · exact mul_zero _
  · simp only [h, ite_false]

/-- The actual retained error outcome determines the test weight in the
recovered ideal support bound, before the complementary key rotation. -/
theorem recovered_observed_zero_row {n : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M)
    (c d : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (r s : Fin (count (BB84SiftedInput.selectedCount M)))
    (i j : (jointSpace (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)).Basis)
    (hr : errorLabel (basis c) i = r)
    (hi : gap < Nat.dist
      (BB84SiftedInput.selectedCount M *
        (c.2.filter (fun l => (Fintype.equivFin (Fin (BB84SiftedInput.selectedCount M) → Fin 2)).symm r l = 1)).card)
      (k * PairwiseSampling.remaining (pairBits i.1) c.1)) :
    (approximant A M k gap hk).matrix (Fintype.equivFin _ c,(r,i))
      (Fintype.equivFin _ d,(s,j)) = 0 := by
  apply recovered_zero_row A M k gap hk c d r s i j
  have hs : selection (basis c) = c.1 :=
    (selectorEquiv (BB84SiftedInput.selectedCount M)).apply_symm_apply c.1
  have ht := PairwiseQuantumSampling.observed_tested (basis c) c.2 i r hr
  rw [hs] at ht
  unfold PairwiseSampling.bad
  rw [show c = (c.1,c.2) from rfl, ht]
  exact hi

/-- The existing finite sampling derivation can include both the measured
record and the physical environment recovery in its postprocessing rule. -/
theorem recovered_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (QuantumSamplingLogic.model
      (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
      (PairwiseQuantumSampling.good k gap) (PairwiseAttackSampling.vector A M)
      (PairwiseAttackSampling.unit A M)
      (fun _ => PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))
      (fun _ => (measurement _ _).seq (recover A M))).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound
          (BB84SiftedInput.selectedCount M) k gap).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ _ (PairwiseAttackSampling.unit A M) _ _
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.errorBound _ k gap).toReal)
  intro _
  exact PairwiseQuantumSampling.classical k gap hk

end
end Foundation.Quantum.QKD.PairwiseRecovery
