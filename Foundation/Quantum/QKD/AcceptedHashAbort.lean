import Foundation.Quantum.QKD.AcceptedHashProcess
import Foundation.Quantum.QKD.SubnormalizedZero

/-! Reading a physical classical output and extracting an impossible
acceptance event yields the zero accepted state, including all quantum blocks. -/
namespace Foundation.Quantum.QKD
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

namespace Subnormalized

theorem readDensity_map {m : Nat} {Y : Type} [Fintype Y] [DecidableEq Y] {e : Space}
    (ρ : Density (.tensor (.register m) e)) (f : Fin m → Y) :
    readDensity ((classicalMap e (fun x => Fintype.equivFin Y (f x))).run ρ) =
      relabel (ofCQ (Guessing.ofDensity ρ)) f := by
  apply State.ext
  funext y
  ext u v
  change (classicalMap e (fun x => Fintype.equivFin Y (f x))).toKraus.apply ρ.matrix
    (Fintype.equivFin Y y,u) (Fintype.equivFin Y y,v) = _
  rw [classicalMap_apply]
  simp only [ite_true, Equiv.apply_eq_iff_eq, relabel, ofCQ, Guessing.ofDensity,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.submatrix_apply, Matrix.zero_apply]

end Subnormalized

namespace AcceptedHash
variable {n length m : Nat} {S : Type} [Fintype S] [DecidableEq S] {e : Space}

theorem process_abort_relabel (ρ : State (Fin m) e) (f : Fin m → RawProtocol.Output n)
    (hf : ∀ x, (f x).transcript.accepted = false) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    process (relabel ρ f) p hash = zero := by
  unfold process
  rw [restrict_relabel]
  rw [restrict_false _ _ (fun x => by simp [hf x]), relabel_zero, seed_zero, relabel_zero]

theorem fromDensity_abort_map (ρ : Density (.tensor (.register m) e)) (f : Fin m → RawProtocol.Output n)
    (hf : ∀ x, (f x).transcript.accepted = false) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    fromDensity ((classicalMap e (fun x => Fintype.equivFin _ (f x))).run ρ) p hash = zero := by
  unfold fromDensity
  rw [readDensity_map]
  exact process_abort_relabel _ _ hf p hash

end AcceptedHash
end
end Foundation.Quantum.QKD
