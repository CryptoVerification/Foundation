import Foundation.Quantum.QKD.PairwiseRawMarginal
import Foundation.Quantum.QKD.BB84SiftedRandomExperiment

/-! Sampling approximation for the entire actual randomized BB84 raw state.
Insufficient-sample branches are kept exactly and contribute zero additional
approximation error; they are not dropped or conditioned away. -/
namespace Foundation.Quantum.QKD.PairwiseRandomizedSampling
noncomputable section
open BB84SiftedInput PairwiseRawSampling
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def conditionalReal {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k minKey tolerance : Nat) :=
  Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis))
    (fun θ => Density.mixture
      (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
      (fun T => (delayedOutput M (joinBases M (θ,η)) e T
        (BB84SiftingRandomness.requiredLength M k minKey) tolerance).run (input A M)))

def conditionalIdeal {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) :=
  if hk : k ≤ selectedCount M then
    marginalIdeal A M η k gap (BB84SiftingRandomness.requiredLength M k minKey) tolerance hk
  else conditionalReal A M η k minKey tolerance

def conditionalError {n : Nat} (M : Finset (Fin n)) (k gap : Nat) : ℝ :=
  if k ≤ selectedCount M then Real.sqrt (PairwiseSampling.errorBound (selectedCount M) k gap).toReal else 0

theorem conditional_approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) :
    StateApprox (conditionalReal A M η k minKey tolerance)
      (conditionalIdeal A M η k gap minKey tolerance) (conditionalError M k gap) := by
  unfold conditionalIdeal conditionalError
  split_ifs with hk
  · have h := marginal_approximation A M η k gap
      (BB84SiftingRandomness.requiredLength M k minKey) tolerance hk
    change OperatorApprox _ _ _ at h
    rw [marginal_delayed] at h
    exact h
  · exact StateApprox.refl _

def ideal {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat) :=
  Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
    Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
      conditionalIdeal A M η k gap minKey tolerance))

def error (n k gap : Nat) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal * conditionalError M k gap

/-- Merely exchanging the order of the independent selected/unmatched bases
recovers the existing full delayed raw experiment, with every guard retained. -/
theorem real_mixture {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
      Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
        conditionalReal A M η k minKey tolerance))).matrix =
      (delayedRecord A k minKey tolerance).matrix := by
  apply Density.mixture_congr_matrix
  intro M
  exact Density.mixture_commute _ _ _

theorem delayed_approximation {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    StateApprox (delayedRecord A k minKey tolerance) (ideal A k gap minKey tolerance) (error n k gap) := by
  have h := StateApprox.mixture (Foundation.Probability.uniform (Finset (Fin n)))
    (fun M => Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalReal A M η k minKey tolerance))
    (fun M => Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalIdeal A M η k gap minKey tolerance))
    (fun M => conditionalError M k gap)
    (fun M => StateApprox.mixture_uniform_bound _ _ _
      (fun η => conditional_approximation A M η k gap minKey tolerance))
  change OperatorApprox _ _ _ at h
  rw [real_mixture] at h
  exact h

/-- The real side is the existing complete independently randomized BB84
prepare/attack raw experiment, with Bob's final signal physically discarded. -/
theorem approximation {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    StateApprox
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (Randomized.record A k minKey tolerance))
      (ideal A k gap minKey tolerance) (error n k gap) := by
  have h := delayed_approximation A k gap minKey tolerance
  change OperatorApprox _ _ _ at h
  rw [delayed_record_eq] at h
  exact h

theorem public_approximation {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    StateApprox (Randomized.publicState A k minKey tolerance)
      ((BB84DeferredRaw.publicChannel n e).run (ideal A k gap minKey tolerance)) (error n k gap) := by
  have h := (delayed_approximation A k gap minKey tolerance).postprocess (BB84DeferredRaw.publicChannel n e)
  change OperatorApprox ((BB84DeferredRaw.publicChannel n e).run (delayedRecord A k minKey tolerance)).matrix _ _ at h
  rw [delayed_public_eq] at h
  exact h

end
end Foundation.Quantum.QKD.PairwiseRandomizedSampling
