import Foundation.Quantum.QKD.PairwisePhasePrivacy
import Foundation.Quantum.QKD.LinearHash

/-! A concrete fresh binary-matrix hash of the complete complementary key.
The detailed error record and the whole auxiliary quantum system remain public
side information. This does not yet remove the publicly tested key positions. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def encode {n : Nat} (x : (qubits n).Basis) : Hashing.Bits (Fin n) :=
  fun i => ZMod.finEquiv 2 (readBits x i)

theorem encode_injective (n : Nat) : Function.Injective (encode (n := n)) := by
  intro x y h
  apply (bitStringEquiv n).injective
  funext i
  exact (ZMod.finEquiv 2).injective (congrFun h i)

def hash {n length : Nat} (s : Hashing.Seed (Fin n) (Fin length))
    (x : (qubits n).Basis) : Hashing.Bits (Fin length) := Hashing.linearHash s (encode x)

theorem collision {n length : Nat} (x y : (qubits n).Basis) (hxy : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform (Hashing.Seed (Fin n) (Fin length)))
      hash x y ≤ 1 / Fintype.card (Hashing.Bits (Fin length)) := by
  have hh := Hashing.linear_collision (O := Fin length) (encode x) (encode y)
    (fun heq => hxy (encode_injective n heq))
  simpa only [Collision.collision, hash, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat] using le_of_eq hh

theorem hashed_distance {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin n) (Fin length)))
        (fun s => Collision.hashed (accepted v hv k gap minKey tolerance c).block (hash s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.Seed (Fin n) (Fin length)))
        (fun _ => Collision.uniformComparator (Y := Hashing.Bits (Fin length))
          (accepted v hv k gap minKey tolerance c).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (Hashing.Bits (Fin length)) *
        ((1-1/Fintype.card (Hashing.Bits (Fin length)))*(bound k gap minKey tolerance c*1)))) :=
  privacy v hv k gap minKey tolerance c _ hash collision

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
