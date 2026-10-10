import Foundation.Quantum.QKD.PairwiseRawHashPrivacy
import Foundation.Quantum.QKD.BB84SiftedOutput

/-! Use the actual full-position BB84 hash seed directly, after restoring
absent unmatched positions. No replacement of the public seed distribution. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem expand_injective {n : Nat} (M : Finset (Fin n)) : Function.Injective (BB84SiftedInput.expand M) := by
  intro x y h
  funext j
  have hj := congrFun h (BB84SiftedInput.indexEmbedding M j)
  simpa only [BB84SiftedInput.expand_index] using hj

def expandedHash {n length : Nat} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M))) (s : Hashing.RawSeed n length)
    (x : (qubits (BB84SiftedInput.remainderCount T)).Basis) : IdealKey.Key length :=
  Hashing.rawHash s (BB84SiftedInput.expand M (optionalKey T x))

theorem expanded_collision {n length : Nat} (M : Finset (Fin n))
    (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (x y : (qubits (BB84SiftedInput.remainderCount T)).Basis) (hxy : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform (Hashing.RawSeed n length)) (expandedHash M T) x y ≤
      1 / Fintype.card (IdealKey.Key length) :=
  le_of_eq (Collision.raw_collision _ _
    (fun h => hxy (optionalKey_injective T (expand_injective M h))))

theorem expandedHashPrivacy {n length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun s => Collision.hashed (testedKey v hv k gap minKey tolerance c).block (expandedHash M c.2 s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (testedKey v hv k gap minKey tolerance c).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) :=
  testedPrivacy v hv k gap minKey tolerance c _ (expandedHash M c.2) (expanded_collision M c.2)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
