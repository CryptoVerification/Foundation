import Foundation.Quantum.QKD.FullReconciledHash

namespace Foundation.Quantum.QKD.FullReconciledHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

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
end Foundation.Quantum.QKD.FullReconciledHash
