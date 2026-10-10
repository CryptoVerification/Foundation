import Foundation.Quantum.QKD.PairwiseAttackSampling
import Foundation.Quantum.RetainedControl

/-! The actual selector-controlled error measurement, with selector/test labels
retained. This is the fixed-reference intermediate experiment, before the
complementary key rotation. The full error record is not declared public by
this construction: publication/discarding must follow the actual protocol. -/
namespace Foundation.Quantum.QKD.PairwiseRecordedSampling
noncomputable section
open PureProjection BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

abbrev output (n : Nat) (e : Space) :=
  Guessing.publicSpace (PairwiseSampling.Configuration n)
    (.tensor (.register (count n)) (jointSpace n e))

def basis {n : Nat} (c : PairwiseSampling.Configuration n) : Fin n → BB84Basis :=
  (BB84PairwiseReference.selectorEquiv n).symm c.1

def measurement (n : Nat) (e : Space) :
    Channel (Guessing.publicSpace (PairwiseSampling.Configuration n) (jointSpace n e))
      (output n e) :=
  RetainedControl.channel (fun t =>
    (PartitionMeasurement.instrument (errorLabel (basis
      ((Fintype.equivFin (PairwiseSampling.Configuration n)).symm t)) (e := e))).record)

theorem apply_public {n : Nat} {e : Space} (p : PMF (PairwiseSampling.Configuration n))
    (A : PairwiseSampling.Configuration n → Operator (jointSpace n e)) :
    (measurement n e).toKraus.apply (publicMixture p A) =
      publicMixture p (fun c =>
        (PartitionMeasurement.instrument (errorLabel (basis c) (e := e))).record.toKraus.apply (A c)) := by
  rw [measurement, RetainedControl.public_apply]
  apply congrArg (publicMixture p)
  funext c
  simp only [Equiv.symm_apply_apply]

def real {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k : Nat) (hk : k ≤ n) : Density (output n e) :=
  (measurement n e).run (QuantumSampling.realState (PairwiseSampling.distribution n k hk) v hv)

def ideal {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) : Density (output n e) :=
  (measurement n e).run (QuantumSampling.idealState (PairwiseSampling.distribution n k hk)
    (PairwiseQuantumSampling.good k gap) v (fun _ => PairwiseQuantumSampling.fallback v hv))

theorem real_eq {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k : Nat) (hk : k ≤ n) :
    (real v hv k hk).matrix = publicMixture (PairwiseSampling.distribution n k hk)
      (fun c => (PartitionMeasurement.instrument (errorLabel (basis c) (e := e))).record.toKraus.apply
        (rank v v)) := apply_public _ _

theorem ideal_eq {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) :
    (ideal v hv k gap hk).matrix = publicMixture (PairwiseSampling.distribution n k hk)
      (fun c => (PartitionMeasurement.instrument (errorLabel (basis c) (e := e))).record.toKraus.apply
        (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
          (PairwiseQuantumSampling.fallback v hv)).matrix) := apply_public _ _

theorem approximation {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) :
    StateApprox (real v hv k hk) (ideal v hv k gap hk)
      (Real.sqrt (PairwiseSampling.errorBound n k gap).toReal) :=
  (PairwiseQuantumSampling.approximation v hv k gap hk).postprocess (measurement n e)

/-- The postprocessing rule now permits a different output space. Its classical
premise is discharged by the proved count, with no extra semantic truth rule. -/
theorem interpreted {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) :
    (QuantumSamplingLogic.model (PairwiseSampling.distribution n k hk)
      (PairwiseQuantumSampling.good k gap) v hv
      (fun _ => PairwiseQuantumSampling.fallback v hv) (fun _ => measurement n e)).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound n k gap).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ v hv _ _
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.errorBound n k gap).toReal)
  intro _
  exact PairwiseQuantumSampling.classical k gap hk

/-- Zero rows hold in the same normalized ideal joint state used in the
approximation, retaining both public labels and the actual detailed outcome. -/
theorem ideal_zero_row {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n)
    (c d : PairwiseSampling.Configuration n) (r s : Fin (count n))
    (i j : (jointSpace n e).Basis) (hi : PairwiseSampling.bad k gap (pairBits i.1) c) :
    (ideal v hv k gap hk).matrix (Fintype.equivFin _ c,(r,i))
      (Fintype.equivFin _ d,(s,j)) = 0 := by
  rw [ideal_eq, publicMixture_block]
  by_cases h : c = d
  · subst d
    simp only [ite_true]
    rw [PartitionMeasurement.record_entry]
    have hz := PairwiseQuantumSampling.supported v hv k gap c i
      (by simpa only [PairwiseQuantumSampling.good, not_not] using hi)
    simp [SupportProjection.state, PureProjection.pure, rank,
      Matrix.vecMulVec_apply, Pi.star_apply, hz]
  · simp only [h, ite_false]

/-- The retained actual outcome supplies the test weight in the support bound.
No division by the probability of the outcome or acceptance is used. -/
theorem observed_zero_row {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n)
    (c d : PairwiseSampling.Configuration n) (r s : Fin (count n))
    (i j : (jointSpace n e).Basis) (hr : errorLabel (basis c) i = r)
    (hi : gap < Nat.dist
      (n * (c.2.filter (fun l => (Fintype.equivFin (Fin n → Fin 2)).symm r l = 1)).card)
      (k * PairwiseSampling.remaining (pairBits i.1) c.1)) :
    (ideal v hv k gap hk).matrix (Fintype.equivFin _ c,(r,i))
      (Fintype.equivFin _ d,(s,j)) = 0 := by
  apply ideal_zero_row v hv k gap hk c d r s i j
  have hs : selection (basis c) = c.1 :=
    (selectorEquiv n).apply_symm_apply c.1
  have ht := PairwiseQuantumSampling.observed_tested (basis c) c.2 i r hr
  rw [hs] at ht
  unfold PairwiseSampling.bad
  rw [show c = (c.1,c.2) from rfl, ht]
  exact hi

end
end Foundation.Quantum.QKD.PairwiseRecordedSampling
