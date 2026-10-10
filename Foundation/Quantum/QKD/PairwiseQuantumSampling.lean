import Foundation.Quantum.QKD.PairwiseSampling
import Foundation.Quantum.QKD.QuantumSamplingLogic

/-! The exact pairwise classical event count is lifted to a normalized,
good-support quantum approximant. Selector and test set remain public.
The actual BB84 fixed-reference input must be used when applying this result. -/
namespace Foundation.Quantum.QKD.PairwiseQuantumSampling
noncomputable section
open PureProjection SupportProjection BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

def good {n : Nat} {e : Space} (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (i : (jointSpace n e).Basis) : Prop :=
  ¬ PairwiseSampling.bad k gap (pairBits i.1) c

instance {n : Nat} {e : Space} (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    DecidablePred (good (e := e) k gap c) := fun _ => inferInstanceAs (Decidable (¬ _))

theorem joint_nonempty {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) : Nonempty (jointSpace n e).Basis := by
  by_contra h
  have : IsEmpty (jointSpace n e).Basis := not_nonempty_iff.mp h
  have hh := (pure v hv).normalized
  norm_num [Matrix.trace, Matrix.diag] at hh

def fallback {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ) (hv : bracket v v = 1) :
    (jointSpace n e).Basis :=
  ((writeBits n (fun _ => 0), writeBits n (fun _ => 0)), (Classical.choice (joint_nonempty v hv)).2)

theorem fallback_good {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    good k gap c (fallback v hv) := by
  simp [good, PairwiseSampling.bad, PairwiseSampling.tested, PairwiseSampling.remaining,
    fallback, pairBits, read_write, Nat.dist_self]

theorem classical {n : Nat} {e : Space} (k gap : Nat) (hk : k ≤ n) (i : (jointSpace n e).Basis) :
    (Foundation.Probability.eventProb (PairwiseSampling.distribution n k hk)
      (fun c => ¬ good k gap c i)).toReal ≤ (PairwiseSampling.errorBound n k gap).toReal := by
  apply ENNReal.toReal_mono (PairwiseSampling.errorBound_finite n k gap)
  simpa only [good, not_not] using PairwiseSampling.classical n k gap hk (pairBits i.1)

/-- No classical bound is assumed: it is obtained from the explicit finite
worst-case count, and coherence is retained in both constructed operators. -/
theorem approximation {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) :
    OperatorApprox (QuantumSampling.real (PairwiseSampling.distribution n k hk) v)
      (QuantumSampling.ideal (PairwiseSampling.distribution n k hk) (good k gap) v
        (fun _ => fallback v hv)) (Real.sqrt (PairwiseSampling.errorBound n k gap).toReal) :=
  QuantumSampling.approximation _ _ v hv _ _ (classical k gap hk)

theorem supported {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (i : (jointSpace n e).Basis) (hi : ¬ good k gap c i) :
    SupportProjection.vector (good k gap c) v (fallback v hv) i = 0 :=
  QuantumSampling.supported (good k gap) v (fun _ => fallback v hv)
    (fun c => fallback_good v hv k gap c) c i hi

/-- Interpret the existing sampling derivation with its classical hypothesis
discharged by the new proved bound, rather than by an assumed quantum truth. -/
theorem interpreted {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n)
    (C : Nat → Channel (Guessing.publicSpace (PairwiseSampling.Configuration n) (jointSpace n e))
      (Guessing.publicSpace (PairwiseSampling.Configuration n) (jointSpace n e))) :
    (QuantumSamplingLogic.model (PairwiseSampling.distribution n k hk) (good k gap) v hv
      (fun _ => fallback v hv) C).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound n k gap).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ v hv _ C
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.errorBound n k gap).toReal)
  intro i
  exact classical k gap hk

/-- The tested reference coordinates are exactly the actual recorded error
bits, rather than an independent or hypothetical classical observation. -/
theorem observed_tested {n : Nat} {e : Space} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (i : (jointSpace n e).Basis) (r : Fin (count n)) (hr : errorLabel θ i = r) :
    PairwiseSampling.tested (pairBits i.1) (selection θ,T) =
      (T.filter (fun j => (Fintype.equivFin (Fin n → Fin 2)).symm r j = 1)).card := by
  have hb : BB84ErrorTransform.errorBits θ i.1 = (Fintype.equivFin (Fin n → Fin 2)).symm r :=
    by simpa only [errorLabel, Equiv.symm_apply_apply] using
      congrArg (Fintype.equivFin (Fin n → Fin 2)).symm hr
  unfold PairwiseSampling.tested
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  rw [← selected_bits, congrFun hb j]

/-- The detailed physical error measurement preserves the ideal support
condition in every row, including coherences against arbitrary other columns. -/
theorem record_zero_row {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (θ : Fin n → BB84Basis) (r : Fin (count n)) (i j : (jointSpace n e).Basis)
    (hi : PairwiseSampling.bad k gap (pairBits i.1) c) :
    ((PartitionMeasurement.instrument (errorLabel θ (e := e))).branch r).apply
      (SupportProjection.state (good k gap c) v (fallback v hv)).matrix i j = 0 := by
  have hz := supported v hv k gap c i (by simpa only [good, not_not] using hi)
  rw [PartitionMeasurement.branch_entry]
  split_ifs <;> simp [SupportProjection.state, PureProjection.pure, rank,
    Matrix.vecMulVec_apply, Pi.star_apply, hz]

/-- After the real error record is known, phase-reference directions whose
weight exceeds the finite deviation criterion have zero amplitude in the
constructed ideal branch. This is not assumed as a privacy hypothesis. -/
theorem observed_zero_row {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (r : Fin (count n)) (i j : (jointSpace n e).Basis) (hr : errorLabel θ i = r)
    (hi : gap < Nat.dist
      (n * (T.filter (fun l => (Fintype.equivFin (Fin n → Fin 2)).symm r l = 1)).card)
      (k * PairwiseSampling.remaining (pairBits i.1) (selection θ))) :
    ((PartitionMeasurement.instrument (errorLabel θ (e := e))).branch r).apply
      (SupportProjection.state (good k gap (selection θ,T)) v (fallback v hv)).matrix i j = 0 := by
  apply record_zero_row v hv k gap (selection θ,T) θ r i j
  unfold PairwiseSampling.bad
  rw [observed_tested θ T i r hr]
  exact hi

end
end Foundation.Quantum.QKD.PairwiseQuantumSampling
