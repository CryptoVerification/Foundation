import Foundation.Quantum.QKD.PairwisePhasePublic

/-! Privacy amplification of the measured sampling approximant. The operator
premise is derived from its physical phase slices, not supplied as an assumption.
The full complementary key is still present; test-key disclosure and restoration
of the protocol's optional raw-key coordinates are separate obligations. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false

theorem privacy {n : Nat} {e : Space} {Y S : Type}
    [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (p : PMF S) (h : S → (qubits n).Basis → Y)
    (hc : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    (PrivacyAmplificationLogic.model p h
      (fun _ => accepted v hv k gap minKey tolerance c)
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
    exact accepted_dominated v hv k gap minKey tolerance c
  · have hi1 : i = 1 := by omega
    subst i
    exact (accepted v hv k gap minKey tolerance c).bounded

/-- Instantiation at the actual arbitrary finite-Kraus attacked source,
with the unmatched signals and dilation environment retained. -/
theorem attacked_dominated {n : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    Subnormalized.Dominated
      (accepted (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
        k gap minKey tolerance c)
      (reference (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap c)
      (bound k gap minKey tolerance c) :=
  accepted_dominated _ _ _ _ _ _ _

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
