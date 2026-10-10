import Foundation.Quantum.QKD.PairwiseAliceState

namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem encode_split {n : Nat} (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) :
    BB84OutcomeCoordinates.encode θ (split n θ (r,z)) = (errorCode r,errorCode z) := by
  have hb := bits n θ (split n θ (r,z))
  rw [split_involution] at hb
  exact Prod.ext (congrArg (Fintype.equivFin (Fin n → Fin 2)) hb.1.symm)
    (congrArg (Fintype.equivFin (Fin n → Fin 2)) hb.2.symm)

/-- The exact original outcome decoder used by the implemented raw protocol
has this Alice coordinate, not merely an abstract isomorphic key type. -/
theorem original_alice {n : Nat} (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) :
    (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).2 = alice n θ r z := by
  rw [BB84OutcomeCoordinates.originalOutcomes, ← encode_split θ r z,
    BB84OutcomeCoordinates.decode_encode]
  exact alice_physical _ _ _ _

theorem aliceState_physical {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    Subnormalized.joint (aliceState v hv k gap c) =
      (classicalMap e (fun t => Fintype.equivFin ((qubits n).Basis × (qubits n).Basis)
        (alicePairEquiv n (PairwiseRecordedSampling.basis c)
          ((Fintype.equivFin ((qubits n).Basis × (qubits n).Basis)).symm t)))).toKraus.apply
        (Subnormalized.joint (Subnormalized.ofCQ (jointState v hv k gap c))) :=
  Subnormalized.relabel_physical _ _

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
