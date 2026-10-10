import Foundation.Quantum.QKD.PairwiseTestExamples

/-! The CQ state used in the phase certificate is exactly a physical complete
measurement of the same sampling approximant, with only the measured signal
discarded. This keeps all auxiliary matrix entries, including coherences. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

def measuredPermutation (n : Nat) (θ : Fin n → BB84Basis) :
    (signal n).Basis ≃ (signal n).Basis :=
  (equivalence n θ).trans (Equiv.prodComm _ _)

def measured {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :=
  (((keyChannel θ).amplify e).seq ((BasisChannel.channel (measuredPermutation n θ)).amplify e)).seq
    (FirstRegister.channel (signal n) e)

theorem measured_joint {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    (jointState v hv k gap c).density.matrix =
      (measured (basis c) e).toKraus.apply
        (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
          (PairwiseQuantumSampling.fallback v hv)).matrix := by
  ext ⟨i,u⟩ ⟨j,w⟩
  obtain ⟨p,rfl⟩ := (Fintype.equivFin ((qubits n).Basis × (qubits n).Basis)).surjective i
  obtain ⟨q,rfl⟩ := (Fintype.equivFin ((qubits n).Basis × (qubits n).Basis)).surjective j
  rw [Guessing.CQ.density_block]
  simp only [measured, Channel.seq, Kraus.seq_apply]
  rw [FirstRegister.apply_entry]
  by_cases hp : p = q
  · subst q
    simp only [ite_true, BasisChannel.amplify_apply, Matrix.of_apply,
      measuredPermutation, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, equivalence, Equiv.coe_fn_symm_mk, Prod.swap]
    exact key_diagonal v hv k gap c p.2 p.1 u w
  · simp only [hp, ite_false]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
