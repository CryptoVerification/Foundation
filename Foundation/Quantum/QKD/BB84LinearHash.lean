import Foundation.Quantum.QKD.LinearHash
import Foundation.Quantum.QKD.BB84Finalization

/-! A concrete two-universal hashing family connected to the actual randomized
BB84 joint state. Optional raw bits use an injective two-bit encoding, so the
collision theorem does not identify an absent position with the value zero.
The quantum leftover-hash and entropy bounds are separate proof obligations. -/
namespace Foundation.Quantum.QKD.Hashing
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Presence and value are separate binary coordinates of each classical raw bit. -/
def encodeRaw {n : Nat} (r : Finalization.RawKey n) : Bits (Fin n × Fin 2) := fun p =>
  if p.2 = 0 then match r p.1 with | none => 0 | some _ => 1
  else match r p.1 with | none => 0 | some v => ZMod.finEquiv 2 v

theorem encodeRaw_injective (n : Nat) : Function.Injective (encodeRaw (n := n)) := by
  intro r s h
  funext i
  have hp := congrFun h (i,0)
  have hv := congrFun h (i,1)
  cases hr : r i with
  | none =>
    cases hs : s i with
    | none => rfl
    | some b => norm_num [encodeRaw,hr,hs] at hp
  | some a =>
    cases hs : s i with
    | none => norm_num [encodeRaw,hr,hs] at hp
    | some b =>
      have hab : a = b := (ZMod.finEquiv 2).injective (by simpa [encodeRaw,hr,hs] using hv)
      rw [hab]

abbrev RawSeed (n length : Nat) := Seed (Fin n × Fin 2) (Fin length)

/-- Binary matrix hashing returns the actual finite key type used by the protocol. -/
def rawHash {n length : Nat} (M : RawSeed n length) (r : Finalization.RawKey n) : IdealKey.Key length :=
  fun i => (ZMod.finEquiv 2).symm (linearHash M (encodeRaw r) i)

/-- Two-universality does not make the output uniform for every fixed input:
 the all-absent raw key is encoded by zero and every linear hash maps it to zero. -/
theorem rawHash_absent_zero {n length : Nat} (M : RawSeed n length) :
    rawHash M (fun _ => none) = (fun _ => 0) := by
  funext i
  have henc : encodeRaw (n := n) (fun _ => none) = 0 := by
    funext p
    simp [encodeRaw]
  simp only [rawHash, henc, linearHash, Matrix.mulVec_zero, Pi.zero_apply, map_zero]

/-- Exact collision probability for every pair of distinct optional raw keys. -/
theorem raw_collision {n length : Nat} (r s : Finalization.RawKey n) (hrs : r ≠ s) :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (RawSeed n length))
      (fun M => rawHash M r = rawHash M s)).toReal = 1 / (2 : ℝ)^length := by
  have heq : (fun M : RawSeed n length => rawHash M r = rawHash M s) =
      (fun M => linearHash M (encodeRaw r) = linearHash M (encodeRaw s)) := by
    funext M
    apply propext
    constructor
    · intro h
      funext i
      exact (ZMod.finEquiv 2).symm.injective (congrFun h i)
    · intro h
      exact congrArg (fun f => fun i => (ZMod.finEquiv 2).symm (f i)) h
  rw [heq]
  simpa only [Fintype.card_fin] using linear_collision (O := Fin length) (encodeRaw r) (encodeRaw s)
    (fun h => hrs (encodeRaw_injective n h))

/-- An actual output density for BB84, with a fresh uniform binary matrix
 announced as a public seed and Eve's whole quantum register retained. -/
def linearState {n length : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (.tensor (IdealKey.register (Finalization.Transcript n (RawSeed n length)) length) e) :=
  Finalization.state A k minKey tolerance (Foundation.Probability.uniform (RawSeed n length)) rawHash

/-- The ideal comparison uses exactly the public-and-adversary state of this
 concrete hashing family; this is not a proof of real-to-ideal closeness. -/
theorem linearState_ideal_public {n length : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((IdealKey.publicChannel e).run (IdealKey.idealize (linearState (length := length) A k minKey tolerance))).matrix =
      ((IdealKey.publicChannel e).run (linearState (length := length) A k minKey tolerance)).matrix :=
  IdealKey.public_idealize _

end
end Foundation.Quantum.QKD.Hashing
