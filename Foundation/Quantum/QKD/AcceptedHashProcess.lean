import Foundation.Quantum.QKD.SubnormalizedMixtureLaws
import Foundation.Quantum.QKD.BB84LinearHash

/-! The actual accepted Alice hash as a specified operation on raw CQ blocks,
with the complete raw public record and independently sampled seed retained. -/
namespace Foundation.Quantum.QKD.AcceptedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {n length : Nat} {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] {e : Space}

def process (ρ : State (RawProtocol.Output n) e) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :=
  relabel (seed p (restrict ρ (fun o => o.transcript.accepted = true)))
    (fun so => (hash so.1 so.2.aliceKey,(so.2.transcript,so.1)))

def fromDensity (ρ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (p : PMF S) (hash : S → Finalization.RawKey n → IdealKey.Key length) :=
  process (readDensity ρ) p hash

theorem process_mixture (q : PMF U) (ρ : U → State (RawProtocol.Output n) e) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    process (mixture q ρ) p hash = mixture q (fun u => process (ρ u) p hash) := by
  unfold process
  rw [mixture_restrict, mixture_seed, mixture_relabel]

theorem fromDensity_mixture (q : PMF U)
    (ρ : U → Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (p : PMF S) (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    fromDensity (Density.mixture q ρ) p hash = mixture q (fun u => fromDensity (ρ u) p hash) := by
  unfold fromDensity
  rw [readDensity_mixture, process_mixture]

theorem fromDensity_CQ (ρ : Guessing.CQ (RawProtocol.Output n) e) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    fromDensity ρ.density p hash = process (ofCQ ρ) p hash := by
  unfold fromDensity
  rw [readDensity_CQ]

theorem fromDensity_congr
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (h : ρ.matrix = σ.matrix) (p : PMF S) (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    fromDensity ρ p hash = fromDensity σ p hash := by
  unfold fromDensity
  rw [readDensity_congr ρ σ h]

end
end Foundation.Quantum.QKD.AcceptedHash
