import Foundation.Quantum.QKD.PairwisePhaseSlices

/-! The operator bound for actual unnormalized error/key measurement branches
of the constructed sampling approximant. The reference covariance and the
measured blocks come from the same state and physical key operation. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open scoped ComplexOrder
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

def errorCode {n : Nat} (r : (qubits n).Basis) : Fin (count n) :=
  Fintype.equivFin (Fin n → Fin 2) (readBits r)

theorem error_split {n : Nat} {e : Space} (θ : Fin n → BB84Basis)
    (r z : (qubits n).Basis) (u : e.Basis) :
    errorLabel θ (split n θ (r,z),u) = errorCode r := by
  have h := (bits n θ (split n θ (r,z))).1
  rw [split_involution] at h
  exact congrArg (Fintype.equivFin (Fin n → Fin 2)) h.symm

def keyBlock {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) : Operator e := Matrix.of (fun u w =>
  ((keyChannel (basis c)).amplify e).toKraus.apply
    (((PartitionMeasurement.instrument (errorLabel (basis c))).branch (errorCode r)).apply
      (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
        (PairwiseQuantumSampling.fallback v hv)).matrix)
      (split n (basis c) (r,z),u) (split n (basis c) (r,z),w))

/-- The actual physical error branch, key rotation and key diagonal have the
coherent supported-amplitude form. No branch-probability normalization. -/
theorem key_block {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) :
    keyBlock v hv k gap c r z = CoherentSupport.outer
      (CoherentSupport.amplitude (phaseSet k gap c r) (PhaseSupport.gate n) (slice v hv k gap c r) z) := by
  ext u w
  change ((keyChannel (basis c)).amplify e).toKraus.apply
    (((PartitionMeasurement.instrument (errorLabel (basis c))).branch (errorCode r)).apply
      (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
        (PairwiseQuantumSampling.fallback v hv)).matrix) _ _ = _
  rw [← branch_key]
  rw [PartitionMeasurement.branch_entry, if_pos ⟨error_split _ _ _ u,error_split _ _ _ w⟩]
  change (Kraus.single (Op.tensor (keyGate (basis c)) (Op.ident e))).apply
    (rank (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
      (PairwiseQuantumSampling.fallback v hv)) _) _ _ = _
  rw [Kraus.single_apply, SourceReplacement.rank_conjugate
    (a := jointSpace n e) (b := jointSpace n e)]
  change rotated (basis c) (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
      (PairwiseQuantumSampling.fallback v hv)) (split n (basis c) (r,z),u) *
    star (rotated (basis c) (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
      (PairwiseQuantumSampling.fallback v hv)) (split n (basis c) (r,z),w)) = _
  rw [supported_amplitude, supported_amplitude]
  rfl

def covariance {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r : (qubits n).Basis) : Operator e :=
  ∑ w ∈ phaseSet k gap c r, CoherentSupport.outer (slice v hv k gap c r w)

/-- The reference certificate is exactly the actual auxiliary marginal in
this error branch, not an unrelated positive matrix chosen as a hypothesis. -/
theorem key_covariance {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r : (qubits n).Basis) :
    (∑ z : (qubits n).Basis, keyBlock v hv k gap c r z) = covariance v hv k gap c r := by
  simp_rw [key_block]
  exact CoherentSupport.measurement_covariance _ _ _ (PhaseSupport.gate_coisometry n)

/-- Cardinality of the actual good phase support divided by 2^n bounds each
actual key block in positive-operator order, with its unnormalized marginal. -/
theorem key_dominated {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) :
    (((((phaseSet k gap c r).card : ℝ) * (1/2:ℝ)^n : ℝ) : ℂ) •
      covariance v hv k gap c r - keyBlock v hv k gap c r z).PosSemidef := by
  rw [key_block]
  exact CoherentSupport.flat_dominated _ _ _ _ (fun w _ => PhaseSupport.gate_flat n w z)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
