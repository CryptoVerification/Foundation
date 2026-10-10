import Foundation.Quantum.QKD.PairwiseReconciledPublicRaw
import Foundation.Quantum.QKD.VerifiedHashLaws

/-! Decode/check/PA directly on an arbitrary physical raw-key density. The
specified public message has a fixed original-position type. This operation
alone asserts no secrecy; the same BB84 support proof supplies the bound. -/
namespace Foundation.Quantum.QKD.ReconciledHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def fixed {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e) (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (relabel (restrict (restrict ρ (fun o => o.transcript.accepted = true))
      (fun o => Hashing.rawHash s (BB84SiftedInput.expand M o.aliceKey) =
        Hashing.rawHash s (BB84SiftedInput.expand M (RawReconciliation.bobKey T o))))
      (RawReconciliation.output T)))
    (fun ro => (Hashing.rawHash ro.1 (BB84SiftedInput.expand M ro.2.aliceKey),
      ((((ro.2.transcript,RawReconciliation.publicMessage M T ro.2),s),
        Hashing.rawHash s (BB84SiftedInput.expand M ro.2.aliceKey)),ro.1)))

def average {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s => fixed (length := length) M T ρ s)

def fromDensity {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : Density (.tensor (.register (Fintype.card (RawProtocol.Output (BB84SiftedInput.selectedCount M)))) e)) :=
  average (tag := tag) (length := length) M T (readDensity ρ)

theorem post_fixed {n tag length : Nat} {a b : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) a) (C : Channel a b) (s : Hashing.RawSeed n tag) :
    post (fixed (length := length) M T ρ s) C = fixed (length := length) M T (post ρ C) s := by
  unfold fixed
  rw [post_relabel, post_seed, post_relabel, post_restrict, post_restrict]

theorem post_average {n tag length : Nat} {a b : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) a) (C : Channel a b) :
    post (average (tag := tag) (length := length) M T ρ) C =
      average (tag := tag) (length := length) M T (post ρ C) := by
  unfold average
  rw [VerifiedHash.post_mixture]
  simp only [post_fixed]

theorem fixed_approx {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ σ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e)
    (s : Hashing.RawSeed n tag) (ε : ℝ) (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (fixed (length := length) M T ρ s)) (joint (fixed (length := length) M T σ s)) ε := by
  unfold fixed
  apply relabel_approx
  apply seed_approx
  apply relabel_approx
  apply restrict_approx
  exact restrict_approx ρ σ _ ε h

theorem average_approx {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ σ : State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e)
    (ε : ℝ) (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (average (tag := tag) (length := length) M T ρ))
      (joint (average (tag := tag) (length := length) M T σ)) ε := by
  have hh := mixture_approx (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => fixed (length := length) M T ρ s) (fun s => fixed (length := length) M T σ s)
    (fun _ => ε) (fun s => fixed_approx M T ρ σ s ε h)
  simpa only [average, ← Finset.sum_mul, Density.probability_weights, one_mul] using hh

theorem fromDensity_approx {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output (BB84SiftedInput.selectedCount M)))) e))
    (ε : ℝ) (h : StateApprox ρ σ ε) :
    OperatorApprox (joint (fromDensity (tag := tag) (length := length) M T ρ))
      (joint (fromDensity (tag := tag) (length := length) M T σ)) ε :=
  average_approx M T _ _ ε (readDensity_approx ρ σ ε h)

theorem fixed_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (p : PMF U)
    (ρ : U → State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e) (s : Hashing.RawSeed n tag) :
    fixed (length := length) M T (mixture p ρ) s = mixture p (fun u => fixed (length := length) M T (ρ u) s) := by
  unfold fixed
  rw [mixture_restrict, mixture_restrict, mixture_relabel, mixture_seed, mixture_relabel]

theorem average_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (p : PMF U)
    (ρ : U → State (RawProtocol.Output (BB84SiftedInput.selectedCount M)) e) :
    average (tag := tag) (length := length) M T (mixture p ρ) =
      mixture p (fun u => average (tag := tag) (length := length) M T (ρ u)) := by
  unfold average
  simp_rw [fixed_mixture]
  exact VerifiedHash.mixture_commute _ _ _

theorem fromDensity_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (p : PMF U)
    (ρ : U → Density (.tensor (.register (Fintype.card (RawProtocol.Output (BB84SiftedInput.selectedCount M)))) e)) :
    fromDensity (tag := tag) (length := length) M T (Density.mixture p ρ) =
      mixture p (fun u => fromDensity (tag := tag) (length := length) M T (ρ u)) := by
  unfold fromDensity
  rw [readDensity_mixture, average_mixture]

end
end Foundation.Quantum.QKD.ReconciledHash

namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem rawHash_process {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    rawHash (length := length) M v hv k gap minKey tolerance c s =
      ReconciledHash.fixed (length := length) M c.2 (ofCQ (rawState v hv k gap minKey tolerance c)) s := rfl

theorem rawAverage_process {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    rawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c =
      ReconciledHash.average (tag := tag) (length := length) M c.2 (ofCQ (rawState v hv k gap minKey tolerance c)) := rfl

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
