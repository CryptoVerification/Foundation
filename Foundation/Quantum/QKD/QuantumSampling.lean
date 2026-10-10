import Foundation.Quantum.SupportProjection
import Foundation.Quantum.RecordObservation

/-! Finite pure-state quantum sampling with an explicit normalized good-support
approximant and public sample record. A pointwise classical error bound is
converted to a square-root quantum observation bound. The predicate and its
combinatorial bound must still be instantiated for BB84 phase sampling. -/
namespace Foundation.Quantum.QKD.QuantumSampling
noncomputable section
open PureProjection SupportProjection
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {a : Space} {S : Type} [Fintype S]

def weight (v : a.Basis → ℂ) (i : a.Basis) : ℝ := (star (v i)*v i).re

theorem weight_nonneg (v : a.Basis → ℂ) (i : a.Basis) : 0 ≤ weight v i :=
  (Complex.nonneg_iff.mp (star_mul_self_nonneg (v i))).1

theorem weight_sum (v : a.Basis → ℂ) : (∑ i, weight v i) = mass v := by
  simp only [weight, mass, bracket, Complex.re_sum]

theorem omitted_mass (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) :
    mass (drop P v) = ∑ i, if P i then 0 else weight v i := by
  simp only [mass, bracket, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P i <;> simp [drop, hi, weight]

/-- Averaging the actual omitted quantum mass uses only the diagonal weights;
coherence is retained in the subsequent comparison of whole operators. -/
theorem average_mass (p : PMF S) (good : S → a.Basis → Prop)
    [∀ s, DecidablePred (good s)] (v : a.Basis → ℂ) (hv : bracket v v = 1) (ε : ℝ)
    (hclass : ∀ i, (Foundation.Probability.eventProb p (fun s => ¬ good s i)).toReal ≤ ε) :
    (∑ s, (p s).toReal * mass (drop (good s) v)) ≤ ε := by
  have hm : mass v = 1 := by rw [mass, hv]; rfl
  have hc (i : a.Basis) : (∑ s, (p s).toReal * (if good s i then (0:ℝ) else 1)) ≤ ε := by
    have hh := hclass i
    rw [eventProb_toReal] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : good s i <;> simp [h]
  simp_rw [omitted_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, weight v i * ∑ s, (p s).toReal * (if good s i then (0:ℝ) else 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : good s i <;> simp [h, mul_comm]
    _ ≤ ∑ i, weight v i * ε := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hc i) (weight_nonneg v i))
    _ = ε := by rw [← Finset.sum_mul, weight_sum, hm, one_mul]

def real (p : PMF S) (v : a.Basis → ℂ) : Operator (Guessing.publicSpace S a) :=
  publicMixture p (fun _ => rank v v)

def ideal (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (fallback : S → a.Basis) : Operator (Guessing.publicSpace S a) :=
  publicMixture p (fun s => (SupportProjection.state (good s) v (fallback s)).matrix)

/-- Both compared operators are genuine normalized public-record states. -/
def realState (p : PMF S) (v : a.Basis → ℂ) (hv : bracket v v = 1) : Density (Guessing.publicSpace S a) where
  matrix := real p v
  positive := publicMixture_positive p _ (fun _ => (pure v hv).positive)
  normalized := by
    rw [real, publicMixture_trace]
    simp only [rank_trace, hv, mul_one]
    norm_cast
    exact Density.probability_weights p

def idealState (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (fallback : S → a.Basis) : Density (Guessing.publicSpace S a) where
  matrix := ideal p good v fallback
  positive := publicMixture_positive p _ (fun s => (SupportProjection.state (good s) v (fallback s)).positive)
  normalized := by
    rw [ideal, publicMixture_trace]
    simp only [(SupportProjection.state _ _ _).normalized, mul_one]
    norm_cast
    exact Density.probability_weights p

/-- A finite version of the square-root sampling estimate for pure joint
states, keeping the sample public and treating zero-good-mass branches. -/
theorem approximation (p : PMF S) (good : S → a.Basis → Prop)
    [∀ s, DecidablePred (good s)] (v : a.Basis → ℂ) (hv : bracket v v = 1)
    (fallback : S → a.Basis) (ε : ℝ)
    (hclass : ∀ i, (Foundation.Probability.eventProb p (fun s => ¬ good s i)).toReal ≤ ε) :
    OperatorApprox (real p v) (ideal p good v fallback) (Real.sqrt ε) := by
  have hh := publicMixture_approx p (fun _ => rank v v)
    (fun s => (SupportProjection.state (good s) v (fallback s)).matrix)
    (fun s => Real.sqrt (mass (drop (good s) v)))
    (fun s => SupportProjection.approximation (good s) v hv (fallback s))
  apply hh.weaken
  exact (probability_sqrt_bound p (fun s => mass (drop (good s) v))
    (fun _ => mass_nonneg _)).trans (Real.sqrt_le_sqrt (average_mass p good v hv ε hclass))

omit [Fintype S] in
/-- Supplying an in-support fallback makes the constructed normalized ideal
vector good even on branches where the original good component vanishes. -/
theorem supported (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (fallback : S → a.Basis) (hf : ∀ s, good s (fallback s))
    (s : S) (j : a.Basis) (hj : ¬ good s j) :
    SupportProjection.vector (good s) v (fallback s) j = 0 :=
  SupportProjection.supported _ v _ (hf s) j hj

/-- Normalization, support and distance are proved for the same constructed
ideal state. The existence of a good basis direction is explicit. -/
theorem sampling (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (hv : bracket v v = 1) (fallback : S → a.Basis)
    (hf : ∀ s, good s (fallback s)) (ε : ℝ)
    (hclass : ∀ i, (Foundation.Probability.eventProb p (fun s => ¬ good s i)).toReal ≤ ε) :
    StateApprox (realState p v hv) (idealState p good v fallback) (Real.sqrt ε) ∧
      ∀ s j, ¬ good s j → SupportProjection.vector (good s) v (fallback s) j = 0 :=
  ⟨approximation p good v hv fallback ε hclass, supported good v fallback hf⟩

/-- The same error bound survives any actual channel on the joint public
record and quantum state, including later measurements and communication. -/
theorem processed {b : Space} (p : PMF S) (good : S → a.Basis → Prop)
    [∀ s, DecidablePred (good s)] (v : a.Basis → ℂ) (hv : bracket v v = 1)
    (fallback : S → a.Basis) (ε : ℝ)
    (hclass : ∀ i, (Foundation.Probability.eventProb p (fun s => ¬ good s i)).toReal ≤ ε)
    (C : Channel (Guessing.publicSpace S a) b) :
    OperatorApprox (C.toKraus.apply (real p v)) (C.toKraus.apply (ideal p good v fallback)) (Real.sqrt ε) :=
  (approximation p good v hv fallback ε hclass).postprocess C

end
end Foundation.Quantum.QKD.QuantumSampling
