import Foundation.Quantum.QKD.VerifiedHashProcess
import Foundation.Quantum.QKD.SeedDistance

/-! The actual two-stage check-and-hash procedure contracts distance. This
includes both acceptance tests and both fresh public seeds, without division
by their passing probability. Full-protocol input bounds remain separate. -/
namespace Foundation.Quantum.QKD.VerifiedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

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

end
end Foundation.Quantum.QKD.VerifiedHash
