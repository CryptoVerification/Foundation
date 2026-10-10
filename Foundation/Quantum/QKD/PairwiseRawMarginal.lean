import Foundation.Quantum.QKD.PairwiseRawSampling
import Foundation.Quantum.PublicMixtureForget

/-! Remove only the extra selector/test copy. The original raw transcript
still contains bases, test positions and outcomes, and Eve remains quantum. -/
namespace Foundation.Quantum.QKD.PairwiseRawSampling
noncomputable section
open BB84PairwiseReference BB84SiftedInput PairwiseRawPost
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def forget (n : Nat) (e : Space) (m : Nat) :=
  Instrument.forgetRecord (rawSpace n e) (Fintype.card (PairwiseSampling.Configuration m))

def marginalReal {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k minKey tolerance : Nat) (hk : k ≤ selectedCount M) :=
  (forget n e (selectedCount M)).run (real A M η k minKey tolerance hk)

def marginalIdeal {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) (hk : k ≤ selectedCount M) :=
  (forget n e (selectedCount M)).run (ideal A M η k gap minKey tolerance hk)

theorem marginal_mixture {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k minKey tolerance : Nat) (hk : k ≤ selectedCount M) :
    (marginalReal A M η k minKey tolerance hk).matrix =
      (Density.mixture (PairwiseSampling.distribution (selectedCount M) k hk)
        (fun c => BB84MixedPreparedRaw.prepared A (joinBases M (PairwiseRecordedSampling.basis c,η))
          (BB84SiftingRandomness.bobBases (joinBases M (PairwiseRecordedSampling.basis c,η)) M)
          (liftTest M c.2) minKey tolerance)).matrix := by
  change (forget n e (selectedCount M)).toKraus.apply _ = _
  rw [real_eq, forget, publicMixture_forget]
  rfl

/-- The actual pair distribution is independent uniform selected bases and
fresh fixed-size nonreplacement testing in the existing delayed experiment. -/
theorem marginal_delayed {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k minKey tolerance : Nat) (hk : k ≤ selectedCount M) :
    (marginalReal A M η k minKey tolerance hk).matrix =
      (Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis))
        (fun θ => Density.mixture
          (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
          (fun T => (delayedOutput M (joinBases M (θ,η)) e T minKey tolerance).run (input A M)))).matrix := by
  rw [marginal_mixture, PairwiseSampling.independent, Density.mixture_bind]
  have hm := Density.mixture_uniform_equiv (selectorEquiv (selectedCount M)).symm
    (fun θ => Density.mixture
      (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
      (fun T => (delayedOutput M (joinBases M (θ,η)) e T minKey tolerance).run (input A M)))
  apply Eq.trans _ hm
  apply Density.mixture_congr_matrix
  intro s
  rw [Density.mixture_map]
  have hd : BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k =
      Sampling.sample Finset.univ k (by simpa using hk) := by
    unfold BB84SiftingRandomness.testDistribution
    rw [dif_pos (by simpa using hk)]
  rw [hd]
  apply Density.mixture_congr_matrix
  intro T
  exact (delayed_prepared A M (joinBases M ((selectorEquiv (selectedCount M)).symm s,η))
    T minKey tolerance).symm

theorem marginal_approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) (hk : k ≤ selectedCount M) :
    StateApprox (marginalReal A M η k minKey tolerance hk)
      (marginalIdeal A M η k gap minKey tolerance hk)
      (Real.sqrt (PairwiseSampling.errorBound (selectedCount M) k gap).toReal) :=
  (approximation A M η k gap minKey tolerance hk).postprocess (forget n e (selectedCount M))

end
end Foundation.Quantum.QKD.PairwiseRawSampling
