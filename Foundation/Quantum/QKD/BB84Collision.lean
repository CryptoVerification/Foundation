import Foundation.Quantum.QKD.CollisionVariance
import Foundation.Quantum.QKD.BB84LinearHash
import Foundation.Quantum.QKD.BB84Accepted

/-! The operator collision estimate for the concrete binary-matrix hashing
family, on the actual accepted BB84 state with all old public data retained.
Fresh seeds are sampled after this input state is fixed. No real-to-ideal
secrecy conclusion is asserted without the remaining distance/entropy proofs. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Exactly the finite pairwise collision probability of the implemented raw-key hash. -/
theorem raw_collision {n length : Nat} (x x' : RawGuess.Key n) (hx : x ≠ x') :
    collision (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash x x' =
      1 / Fintype.card (IdealKey.Key length) := by
  simpa only [collision, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    Hashing.raw_collision (length := length) x x' hx

/-- The previous public transcript is quantum side information in the collision calculation. -/
def acceptedInput {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Subnormalized.State (RawGuess.Key n) (Guessing.publicSpace (RawProtocol.PublicRecord n) e) :=
  Subnormalized.withPublic (Accepted.state A k minKey tolerance)

/-- Each hashed branch is a real trace-preserving classical channel acting
on this accepted joint operator, while keeping the old public record and Eve. -/
theorem accepted_hash_physical {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) (seed : Hashing.RawSeed n length) :
    Subnormalized.joint (Subnormalized.relabel (acceptedInput A k minKey tolerance) (Hashing.rawHash seed)) =
      (classicalMap _ (fun t => Fintype.equivFin (IdealKey.Key length)
        (Hashing.rawHash seed ((Fintype.equivFin (RawGuess.Key n)).symm t)))).toKraus.apply
          (Subnormalized.joint (acceptedInput A k minKey tolerance)) :=
  Subnormalized.relabel_physical _ _

/-- No restriction on the conjugation or on the adversary's finite dimension
is imposed by this collision step. Inverse-root/support witnesses are separate. -/
theorem accepted_weighted_variance {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) (K : Operator (Guessing.publicSpace (RawProtocol.PublicRecord n) e)) :
    variance (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash
      (sandwich K (acceptedInput A k minKey tolerance).block) ≤
        (1 - 1 / Fintype.card (IdealKey.Key length)) *
          input (sandwich K (acceptedInput A k minKey tolerance).block) := by
  apply variance_sharp_le _ _ _ (sandwich_positive K _ (acceptedInput A k minKey tolerance).positive)
  intro x x' hx
  exact le_of_eq (raw_collision x x' hx)

end
end Foundation.Quantum.QKD.Collision
