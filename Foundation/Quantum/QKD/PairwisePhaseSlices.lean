import Foundation.Quantum.QKD.PairwisePhaseAmplitude

/-! Explicit complementary-support slices of the same normalized sampling
approximant. Error branches are not renormalized, including zero branches. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open scoped ComplexOrder
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

def phaseSet {n : Nat} (k gap : Nat) (c : PairwiseSampling.Configuration n) (r : (qubits n).Basis) :
    Finset (qubits n).Basis :=
  Finset.univ.filter (fun z => ¬PairwiseSampling.bad k gap (pairBits (split n (basis c) (r,z))) c)

def slice {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) : e.Basis → ℂ := fun u =>
  SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
    (PairwiseQuantumSampling.fallback v hv) (split n (basis c) (r,z),u)

theorem slice_supported {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) (hz : z ∉ phaseSet k gap c r) (u : e.Basis) :
    slice v hv k gap c r z u = 0 := by
  apply PairwiseQuantumSampling.supported v hv k gap c _
  simpa only [phaseSet, Finset.mem_filter, Finset.mem_univ, true_and,
    PairwiseQuantumSampling.good] using hz

/-- The actual physical key operation synthesizes only the supported phase
slices; the zero-mass error branch needs no separate choice or division. -/
theorem supported_amplitude {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) (u : e.Basis) :
    rotated (basis c) (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
      (PairwiseQuantumSampling.fallback v hv)) (split n (basis c) (r,z),u) =
      CoherentSupport.amplitude (phaseSet k gap c r) (PhaseSupport.gate n) (slice v hv k gap c r) z u := by
  rw [rotated_amplitude]
  change (∑ w : (qubits n).Basis, PhaseSupport.gate n z w * slice v hv k gap c r w u) = _
  calc
    _ = ∑ w ∈ phaseSet k gap c r, PhaseSupport.gate n z w * slice v hv k gap c r w u := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      rw [slice_supported v hv k gap c r w hw u, mul_zero]
    _ = _ := by
      simp only [CoherentSupport.amplitude, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro w _
      rw [PhaseSupport.gate_symmetric n z w]

/-- An actual positive operator certificate, not a guessing/secrecy premise.
The reference covariance is subnormalized with the error branch. -/
theorem slice_dominated {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) :
    (((((phaseSet k gap c r).card : ℝ) * (1/2:ℝ)^n : ℝ) : ℂ) •
      (∑ w ∈ phaseSet k gap c r, CoherentSupport.outer (slice v hv k gap c r w)) -
      CoherentSupport.outer (fun u =>
        rotated (basis c) (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
          (PairwiseQuantumSampling.fallback v hv)) (split n (basis c) (r,z),u))).PosSemidef := by
  have ha : (fun u => rotated (basis c)
      (SupportProjection.vector (PairwiseQuantumSampling.good k gap c) v
        (PairwiseQuantumSampling.fallback v hv)) (split n (basis c) (r,z),u)) =
      CoherentSupport.amplitude (phaseSet k gap c r) (PhaseSupport.gate n) (slice v hv k gap c r) z := by
    funext u
    exact supported_amplitude v hv k gap c r z u
  rw [ha]
  exact CoherentSupport.flat_dominated _ _ _ _ (fun w _ => PhaseSupport.gate_flat n w z)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
