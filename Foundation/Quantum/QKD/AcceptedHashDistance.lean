import Foundation.Quantum.QKD.AcceptedHashProcess
import Foundation.Quantum.QKD.UniformKeyDistance

/-! The actual accepted hash contracts raw-state observation distance.
The accepted branch is never divided by its probability. -/
namespace Foundation.Quantum.QKD.AcceptedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {n length : Nat} {S : Type} [Fintype S] [DecidableEq S] {e : Space}

theorem process_approx (ρ σ : State (RawProtocol.Output n) e) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (process ρ p hash)) (joint (process σ p hash)) ε := by
  unfold process
  apply relabel_approx
  apply seed_approx
  exact restrict_approx ρ σ _ ε h

theorem fromDensity_approx
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) (ε : ℝ) (h : StateApprox ρ σ ε) :
    OperatorApprox (joint (fromDensity ρ p hash)) (joint (fromDensity σ p hash)) ε :=
  process_approx _ _ p hash ε (readDensity_approx ρ σ ε h)

end
end Foundation.Quantum.QKD.AcceptedHash
