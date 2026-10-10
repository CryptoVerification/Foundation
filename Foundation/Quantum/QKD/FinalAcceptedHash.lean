import Foundation.Quantum.QKD.AcceptedHashProcess
import Foundation.Quantum.QKD.SubnormalizedEquiv
import Foundation.Quantum.QKD.BB84FinalSecurity

/-! The accepted Alice hash obtained from the actual raw density is exactly
the Alice view of the existing accepted finalization branch, not a new output
experiment. Original classical labels, public seed and Eve blocks agree. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Subnormalized

theorem readDensity_fin_relabel {X : Type} [Fintype X] [DecidableEq X] {e : Space}
    (ρ : Density (.tensor (.register (Fintype.card X)) e)) :
    readDensity (X := X) ρ = relabel (ofCQ (Guessing.ofDensity ρ)) (Fintype.equivFin X).symm := by
  apply State.ext
  funext x
  rw [relabel_equiv_block]
  rfl

end Subnormalized
namespace FinalSecurity
open Subnormalized
variable {n length : Nat} {S : Type} [Fintype S] [DecidableEq S] {e : Space}

theorem alice_accepted_hash (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    AcceptedHash.fromDensity (Randomized.keyState A k minKey tolerance) p hash =
      CommonKey.aliceView (acceptedBranch A k minKey tolerance p hash) := by
  unfold AcceptedHash.fromDensity AcceptedHash.process
  rw [readDensity_fin_relabel, restrict_relabel, seed_relabel, relabel_comp, seed_restrict]
  unfold CommonKey.aliceView acceptedBranch
  rw [relabel_comp]
  rfl

end FinalSecurity
end
end Foundation.Quantum.QKD
