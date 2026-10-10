import Foundation.Quantum.QKD.FullRawReconciliation
import Foundation.Quantum.QKD.ReconciledHashProcess

/-! The same specified reconciliation/check/PA directly on the original
full BB84 raw state. Sifting and testing are read from its public record;
no chosen subset or sampling configuration is an external input. -/
namespace Foundation.Quantum.QKD.FullReconciledHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def fixed {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (restrict ρ (fun o => o.transcript.accepted = true))
      (fun o => Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey)))
    (fun ro => (Hashing.rawHash ro.1 ro.2.aliceKey,
      ((((ro.2.transcript,FullRawReconciliation.publicMessage ro.2),s),Hashing.rawHash s ro.2.aliceKey),ro.1)))

def average {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s => fixed (length := length) ρ s)

def fromDensity {n tag length : Nat} {e : Space}
    (ρ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) :=
  average (tag := tag) (length := length) (readDensity ρ)

theorem post_fixed {n tag length : Nat} {a b : Space} (ρ : State (RawProtocol.Output n) a)
    (C : Channel a b) (s : Hashing.RawSeed n tag) :
    post (fixed (length := length) ρ s) C = fixed (length := length) (post ρ C) s := by
  unfold fixed
  rw [post_relabel, post_seed, post_restrict, post_restrict]

theorem post_average {n tag length : Nat} {a b : Space} (ρ : State (RawProtocol.Output n) a)
    (C : Channel a b) :
    post (average (tag := tag) (length := length) ρ) C = average (tag := tag) (length := length) (post ρ C) := by
  unfold average
  rw [VerifiedHash.post_mixture]
  simp only [post_fixed]

theorem fixed_approx {n tag length : Nat} {e : Space} (ρ σ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) (ε : ℝ) (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (fixed (length := length) ρ s)) (joint (fixed (length := length) σ s)) ε := by
  unfold fixed
  apply relabel_approx
  apply seed_approx
  apply restrict_approx
  exact restrict_approx ρ σ _ ε h

theorem average_approx {n tag length : Nat} {e : Space} (ρ σ : State (RawProtocol.Output n) e)
    (ε : ℝ) (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (average (tag := tag) (length := length) ρ))
      (joint (average (tag := tag) (length := length) σ)) ε := by
  have hh := mixture_approx (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => fixed (length := length) ρ s) (fun s => fixed (length := length) σ s)
    (fun _ => ε) (fun s => fixed_approx ρ σ s ε h)
  simpa only [average, ← Finset.sum_mul, Density.probability_weights, one_mul] using hh

theorem fromDensity_approx {n tag length : Nat} {e : Space}
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (ε : ℝ) (h : StateApprox ρ σ ε) :
    OperatorApprox (joint (fromDensity (tag := tag) (length := length) ρ))
      (joint (fromDensity (tag := tag) (length := length) σ)) ε :=
  average_approx _ _ ε (readDensity_approx ρ σ ε h)

theorem fixed_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (p : PMF U) (ρ : U → State (RawProtocol.Output n) e) (s : Hashing.RawSeed n tag) :
    fixed (length := length) (mixture p ρ) s = mixture p (fun u => fixed (length := length) (ρ u) s) := by
  unfold fixed
  rw [mixture_restrict, mixture_restrict, mixture_seed, mixture_relabel]

theorem average_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (p : PMF U) (ρ : U → State (RawProtocol.Output n) e) :
    average (tag := tag) (length := length) (mixture p ρ) =
      mixture p (fun u => average (tag := tag) (length := length) (ρ u)) := by
  unfold average
  simp_rw [fixed_mixture]
  exact VerifiedHash.mixture_commute _ _ _

theorem fromDensity_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (p : PMF U) (ρ : U → Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) :
    fromDensity (tag := tag) (length := length) (Density.mixture p ρ) =
      mixture p (fun u => fromDensity (tag := tag) (length := length) (ρ u)) := by
  unfold fromDensity
  rw [readDensity_mixture, average_mixture]

theorem fromDensity_congr {n tag length : Nat} {e : Space}
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) (h : ρ.matrix = σ.matrix) :
    fromDensity (tag := tag) (length := length) ρ = fromDensity (tag := tag) (length := length) σ := by
  unfold fromDensity
  rw [readDensity_congr ρ σ h]

end
end Foundation.Quantum.QKD.FullReconciledHash
