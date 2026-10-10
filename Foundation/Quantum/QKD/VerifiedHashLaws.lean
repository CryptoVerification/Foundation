import Foundation.Quantum.QKD.VerifiedHashDistance
import Foundation.Quantum.QKD.AcceptedHashAbort
import Foundation.Quantum.QKD.ZeroSecrecy

/-! Linearity in the actual branch weights and impossible accepted events
for the same two independently seeded check-and-hash process. -/
namespace Foundation.Quantum.QKD.VerifiedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem mixture_commute {S U X : Type} [Fintype S] [Fintype U] [Fintype X]
    {e : Space} (p : PMF S) (q : PMF U) (ρ : S → U → State X e) :
    mixture p (fun s => mixture q (ρ s)) = mixture q (fun u => mixture p (fun s => ρ s u)) := by
  apply State.ext
  funext x
  simp only [mixture, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem fixed_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (q : PMF U) (ρ : U → State (RawProtocol.Output n) e) (s : Hashing.RawSeed n tag) :
    fixed (length := length) (mixture q ρ) s = mixture q (fun u => fixed (length := length) (ρ u) s) := by
  unfold fixed
  rw [mixture_restrict, mixture_restrict, mixture_seed, mixture_relabel]

theorem average_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (q : PMF U) (ρ : U → State (RawProtocol.Output n) e) :
    average (tag := tag) (length := length) (mixture q ρ) =
      mixture q (fun u => average (tag := tag) (length := length) (ρ u)) := by
  unfold average
  simp_rw [fixed_mixture]
  exact mixture_commute _ _ _

theorem fromDensity_mixture {n tag length : Nat} {U : Type} [Fintype U] {e : Space}
    (q : PMF U) (ρ : U → Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) :
    fromDensity (tag := tag) (length := length) (Density.mixture q ρ) =
      mixture q (fun u => fromDensity (tag := tag) (length := length) (ρ u)) := by
  unfold fromDensity
  rw [readDensity_mixture, average_mixture]

theorem fromDensity_congr {n tag length : Nat} {e : Space}
    (ρ σ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (h : ρ.matrix = σ.matrix) :
    fromDensity (tag := tag) (length := length) ρ = fromDensity (tag := tag) (length := length) σ := by
  unfold fromDensity
  rw [readDensity_congr ρ σ h]

theorem fixed_abort_relabel {n tag length m : Nat} {e : Space}
    (ρ : State (Fin m) e) (f : Fin m → RawProtocol.Output n)
    (hf : ∀ x, (f x).transcript.accepted = false) (s : Hashing.RawSeed n tag) :
    fixed (length := length) (relabel ρ f) s = zero := by
  have ha : restrict (relabel ρ f) (fun o => o.transcript.accepted = true) = zero := by
    rw [restrict_relabel, restrict_false _ _ (fun x => by simp [hf x]), relabel_zero]
  unfold fixed
  rw [ha]
  have hz (P : RawProtocol.Output n → Prop) [DecidablePred P] :
      restrict (zero : State (RawProtocol.Output n) e) P = zero := by
    apply State.ext
    funext x
    simp [restrict, zero]
  rw [hz, seed_zero, relabel_zero]

theorem fromDensity_abort_map {n tag length m : Nat} {e : Space}
    (ρ : Density (.tensor (.register m) e)) (f : Fin m → RawProtocol.Output n)
    (hf : ∀ x, (f x).transcript.accepted = false) :
    fromDensity (tag := tag) (length := length)
      ((classicalMap e (fun x => Fintype.equivFin _ (f x))).run ρ) = zero := by
  unfold fromDensity average
  rw [readDensity_map]
  simp_rw [fixed_abort_relabel _ _ hf]
  exact mixture_zero _

end
end Foundation.Quantum.QKD.VerifiedHash
