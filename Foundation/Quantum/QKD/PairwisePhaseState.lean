import Foundation.Quantum.QKD.PairwisePhaseBand
import Foundation.Quantum.QKD.CQRepresentation

/-! The actual unnormalized error/key blocks form a normalized CQ state.
Its error-labelled marginal will supply the normalized reference required by
privacy amplification, without normalizing each measurement outcome. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

theorem key_diagonal {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) (u w : e.Basis) :
    keyBlock v hv k gap c r z u w =
      (((keyChannel (basis c)).amplify e).run
        (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
          (PairwiseQuantumSampling.fallback v hv))).matrix
          (split n (basis c) (r,z),u) (split n (basis c) (r,z),w) := by
  change ((keyChannel (basis c)).amplify e).toKraus.apply
    (((PartitionMeasurement.instrument (errorLabel (basis c))).branch (errorCode r)).apply
      (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
        (PairwiseQuantumSampling.fallback v hv)).matrix) _ _ = _
  rw [← branch_key, PartitionMeasurement.branch_entry,
    if_pos ⟨error_split _ _ _ u,error_split _ _ _ w⟩]
  rfl

theorem blocks_normalized {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    (∑ p : (qubits n).Basis × (qubits n).Basis, (keyBlock v hv k gap c p.1 p.2).trace) = 1 := by
  let ρ := ((keyChannel (basis c)).amplify e).run
    (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v (PairwiseQuantumSampling.fallback v hv))
  calc
    _ = ∑ p : (signal n).Basis, ∑ u : e.Basis,
        ρ.matrix (split n (basis c) p,u) (split n (basis c) p,u) := by
      apply Finset.sum_congr rfl
      intro p _
      unfold Matrix.trace Matrix.diag
      apply Finset.sum_congr rfl
      intro u _
      exact key_diagonal v hv k gap c p.1 p.2 u u
    _ = ∑ p : (signal n).Basis, ∑ u : e.Basis, ρ.matrix (p,u) (p,u) :=
      Equiv.sum_comp (equivalence n (basis c)) (fun p => ∑ u : e.Basis, ρ.matrix (p,u) (p,u))
    _ = 1 := by
      have h := ρ.normalized
      simpa only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using h

/-- The ordering is key first, error record second, as needed for public
side-information packaging. The blocks are the actual physical branches. -/
def jointState {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    Guessing.CQ ((qubits n).Basis × (qubits n).Basis) e where
  block p := keyBlock v hv k gap c p.2 p.1
  positive p := by rw [key_block]; exact CoherentSupport.outer_positive _
  normalized := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using blocks_normalized v hv k gap c

/-- The reference is a genuine normalized state with the detailed error
record retained next to Eve; branch probabilities remain in its blocks. -/
def reference {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    Density (Guessing.publicSpace (qubits n).Basis e) :=
  Guessing.marginal (Guessing.withPublic (jointState v hv k gap c))

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
