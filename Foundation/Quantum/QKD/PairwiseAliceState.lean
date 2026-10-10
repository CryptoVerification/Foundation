import Foundation.Quantum.QKD.PairwiseAliceCoordinates
import Foundation.Quantum.QKD.SubnormalizedEquiv

/-! Alice's full original key, obtained by a physical classical permutation
of the same sampling approximant's complementary key and error record. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false

def aliceState {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap : Nat) (c : PairwiseSampling.Configuration n) :=
  Subnormalized.relabel (Subnormalized.ofCQ (jointState v hv k gap c))
    (alicePairEquiv n (PairwiseRecordedSampling.basis c))

theorem aliceState_block {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap : Nat) (c : PairwiseSampling.Configuration n) (x r : (qubits n).Basis) :
    (aliceState v hv k gap c).block (x,r) =
      keyBlock v hv k gap c r (alice n (PairwiseRecordedSampling.basis c) r x) := by
  unfold aliceState
  rw [Subnormalized.relabel_equiv_block]
  rfl

theorem aliceState_mass {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    Subnormalized.mass (aliceState v hv k gap c) = 1 := by
  rw [aliceState, Subnormalized.mass_relabel]
  simpa only [Subnormalized.mass, Subnormalized.ofCQ, Complex.re_sum, Complex.one_re] using
    congrArg Complex.re (jointState v hv k gap c).normalized

def acceptedAlice {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :=
  Subnormalized.withPublic (Subnormalized.restrict (aliceState v hv k gap c)
    (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2)))

theorem acceptedAlice_block {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (x : (qubits n).Basis) :
    (acceptedAlice v hv k gap minKey tolerance c).block x =
      ∑ r : (qubits n).Basis, Matrix.kronecker
        (basisDensity (.register (Fintype.card (qubits n).Basis)) (Fintype.equivFin (qubits n).Basis r)).matrix
        (if BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)
         then keyBlock v hv k gap c r (alice n (PairwiseRecordedSampling.basis c) r x) else 0) := by
  simp only [acceptedAlice, Subnormalized.withPublic, Subnormalized.restrict, aliceState_block]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
