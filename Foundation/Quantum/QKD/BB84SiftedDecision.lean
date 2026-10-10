import Foundation.Quantum.QKD.BB84SiftedTests

/-! The actual raw BB84 test and acceptance predicate are preserved by
reindexing matched positions. Both arbitrary tolerances and length guards
remain explicit; bit errors are not identified with phase errors. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def bits {n : Nat} (M : Finset (Fin n)) (b : Fin n → Fin 2) :
    Fin (selectedCount M) → Fin 2 := fun i => b (indexEmbedding M i)

theorem restrict_filter {n : Nat} (M T : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    restrictTest M (T.filter P) = (restrictTest M T).filter (fun i => P (indexEmbedding M i)) := by
  ext i
  simp [restrictTest]

theorem errors_eq {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M) (b c : Fin n → Fin 2) :
    RawProtocol.errors (bits M b) (bits M c) (restrictTest M T) = RawProtocol.errors b c T := by
  unfold RawProtocol.errors bits
  rw [← restrict_filter M T (fun i => b i ≠ c i),
    restrict_card M _ ((Finset.filter_subset _ _).trans hT)]

theorem restrict_sdiff {n : Nat} (M T : Finset (Fin n)) :
    restrictTest M (M \ T) = Finset.univ \ restrictTest M T := by
  ext i
  simp [restrictTest, indexEmbedding]

theorem key_card {n : Nat} (M T : Finset (Fin n)) :
    (Finset.univ \ restrictTest M T).card = (M \ T).card := by
  rw [← restrict_sdiff, restrict_card M _ Finset.sdiff_subset]

theorem accepts_eq {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M)
    (θ : Fin n → BB84Basis) (b c : Fin n → Fin 2) (minKey tolerance : Nat) :
    RawProtocol.accepts θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance =
      RawProtocol.accepts (bases M θ) (bases M θ) (bits M b) (bits M c)
        (restrictTest M T) minKey tolerance := by
  have hm : RawProtocol.matched (bases M θ) (bases M θ) = Finset.univ := by
    simp [RawProtocol.matched]
  unfold RawProtocol.accepts RawProtocol.keyPositions
  rw [BB84SiftingRandomness.matched_bob, hm, key_card, errors_eq M T hT]
  simp only [hT, Finset.subset_univ, true_and]

theorem requiredLength_eq {n : Nat} (M : Finset (Fin n)) (k minKey : Nat) :
    BB84SiftingRandomness.requiredLength (Finset.univ : Finset (Fin (selectedCount M))) k minKey =
      BB84SiftingRandomness.requiredLength M k minKey := by
  simp only [BB84SiftingRandomness.requiredLength, Finset.card_univ, Fintype.card_fin,
    selectedCount_eq_card]

theorem key_mem {n : Nat} (M T : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (i : Fin (selectedCount M)) :
    indexEmbedding M i ∈ RawProtocol.keyPositions θ (BB84SiftingRandomness.bobBases θ M) T ↔
      i ∈ RawProtocol.keyPositions (bases M θ) (bases M θ) (restrictTest M T) := by
  unfold RawProtocol.keyPositions
  rw [BB84SiftingRandomness.matched_bob]
  have hm : RawProtocol.matched (bases M θ) (bases M θ) = Finset.univ := by simp [RawProtocol.matched]
  rw [hm]
  simp [restrictTest, indexEmbedding]

/-- Both private raw keys, including their erasure on abort, are preserved
at every matched position by the actual output constructor. -/
theorem private_keys {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M)
    (θ : Fin n → BB84Basis) (b c : Fin n → Fin 2) (minKey tolerance : Nat)
    (i : Fin (selectedCount M)) :
    (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance).aliceKey
        (indexEmbedding M i) =
      (RawProtocol.output (bases M θ) (bases M θ) (bits M b) (bits M c)
        (restrictTest M T) minKey tolerance).aliceKey i ∧
    (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance).bobKey
        (indexEmbedding M i) =
      (RawProtocol.output (bases M θ) (bases M θ) (bits M b) (bits M c)
        (restrictTest M T) minKey tolerance).bobKey i := by
  simp [RawProtocol.output, accepts_eq M T hT, key_mem, bits]

end
end Foundation.Quantum.QKD.BB84SiftedInput
