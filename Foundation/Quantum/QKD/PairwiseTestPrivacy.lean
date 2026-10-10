import Foundation.Quantum.QKD.PairwiseTestKey

/-! Privacy amplification of the remaining key with test values public,
and an explicit bound for a subsequently disclosed binary syndrome. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false

theorem testedPrivacy {n : Nat} {e : Space} {Y S : Type}
    [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (p : PMF S) (h : S → (qubits (BB84SiftedInput.remainderCount c.2)).Basis → Y)
    (hc : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    (PrivacyAmplificationLogic.model p h
      (fun _ => testedKey v hv k gap minKey tolerance c)
      (fun _ => Subnormalized.leakedReference
        (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis) (reference v hv k gap c)) hc).Carrier
      (.distance 0 ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1))))) := by
  apply PrivacyAmplificationLogic.sound p h _ _ hc
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0
      ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) 1 _
      (mul_nonneg (by positivity) (bound_nonneg _ _ _ _ _)) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact tested_dominated v hv k gap minKey tolerance c
  · have hi1 : i = 1 := by omega
    subst i
    exact (testedKey v hv k gap minKey tolerance c).bounded

/-- Any specified m-bit message of the remaining key has this leakage cost.
This theorem supplies neither an error-correcting decoder nor correctness. -/
theorem syndrome_dominated {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance m : Nat) (c : PairwiseSampling.Configuration n)
    (syndrome : (qubits (BB84SiftedInput.remainderCount c.2)).Basis → (Fin m → Fin 2)) :
    Subnormalized.Dominated
      (Subnormalized.withPublic (Subnormalized.withPublic (Subnormalized.disclose
        (Subnormalized.relabel (acceptedAlice v hv k gap minKey tolerance c) (testEquiv c.2))
        (fun x _ => syndrome x))))
      (Subnormalized.leakedReference (C := Fin m → Fin 2)
        (Subnormalized.leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
          (reference v hv k gap c)))
      ((2:ℝ)^m * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) :=
  Subnormalized.bit_disclose_dominated m _ _ _ _ (tested_dominated v hv k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
