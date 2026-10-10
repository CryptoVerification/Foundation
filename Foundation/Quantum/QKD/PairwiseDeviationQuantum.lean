import Foundation.Quantum.QKD.PairwiseDeviationSplit
import Foundation.Quantum.QKD.PairwiseQuantumSampling

/-! The proved two-component bound interpreted by the existing finite
sampling logic on the same coherent reference state. The unproved second
analytic estimate is left as an exact finite maximum, not as an axiom. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Exact residual event for fixed-size sampling without replacement. -/
def sampleTailBound (n k : Nat) (hk : k ≤ n) (u : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : Pattern n =>
    (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal)

theorem sampleTailBound_le (n k : Nat) (hk : k ≤ n) (u : ℝ) (q : Pattern n) :
    (eventProb (distribution n k hk) (fun c => u < |sampleDifference k q c|)).toReal ≤
      sampleTailBound n k hk u := by
  unfold sampleTailBound
  exact Finset.le_sup' (fun r : Pattern n =>
    (eventProb (distribution n k hk) (fun c => u < |sampleDifference k r c|)).toReal)
      (Finset.mem_univ q)

def separatedBound (n k : Nat) (hk : k ≤ n) (u t : ℝ) : ℝ :=
  n / t^2 + sampleTailBound n k hk u

theorem classical_separated (n k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap) (q : Pattern n) :
    (eventProb (distribution n k hk) (bad k gap q)).toReal ≤ separatedBound n k hk u t := by
  have h := classical_decomposition_bound k gap hk q u t ht hgap
  have hmax := sampleTailBound_le n k hk u q
  unfold separatedBound
  linarith

end
end Foundation.Quantum.QKD.PairwiseSampling

namespace Foundation.Quantum.QKD.PairwiseQuantumSampling
noncomputable section
open PureProjection BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

theorem classical_separated {n : Nat} {e : Space} (k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap) (i : (jointSpace n e).Basis) :
    (Foundation.Probability.eventProb (PairwiseSampling.distribution n k hk)
      (fun c => ¬ good k gap c i)).toReal ≤ PairwiseSampling.separatedBound n k hk u t := by
  simpa only [good, not_not] using PairwiseSampling.classical_separated n k gap hk u t ht hgap (pairBits i.1)

theorem approximation_separated {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap) :
    OperatorApprox (QuantumSampling.real (PairwiseSampling.distribution n k hk) v)
      (QuantumSampling.ideal (PairwiseSampling.distribution n k hk) (good k gap) v
        (fun _ => fallback v hv)) (Real.sqrt (PairwiseSampling.separatedBound n k hk u t)) :=
  QuantumSampling.approximation _ _ v hv _ _ (classical_separated k gap hk u t ht hgap)

/-- The existing concrete lift/post derivation; its sole classical premise
is supplied by the coordinate-flip moment and union-bound proofs above. -/
theorem interpreted_separated {n : Nat} {e b : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (hk : k ≤ n) (u t : ℝ)
    (ht : 0 < t) (hgap : u + k*t ≤ gap)
    (C : Nat → Channel (Guessing.publicSpace (PairwiseSampling.Configuration n) (jointSpace n e)) b) :
    (QuantumSamplingLogic.model (PairwiseSampling.distribution n k hk) (good k gap) v hv
      (fun _ => fallback v hv) C).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.separatedBound n k hk u t))) := by
  apply QuantumSamplingLogic.sound _ _ v hv _ C
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.separatedBound n k hk u t))
  intro _
  exact classical_separated k gap hk u t ht hgap

end
end Foundation.Quantum.QKD.PairwiseQuantumSampling
