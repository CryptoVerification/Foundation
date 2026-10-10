import Foundation.Quantum.QKD.BB84SiftedDecision

/-! Restore the original public/raw-key record from selected-position data.
The public original bases are supplied explicitly. Unmatched private values
are absent; no extra key data is silently leaked by reconstruction. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def expand {n : Nat} (M : Finset (Fin n)) (v : Fin (selectedCount M) → Option (Fin 2)) :
    Fin n → Option (Fin 2) := fun i =>
  if h : i ∈ M then v ((selectedIndex M).symm ⟨i,h⟩) else none

theorem expand_index {n : Nat} (M : Finset (Fin n))
    (v : Fin (selectedCount M) → Option (Fin 2)) (j : Fin (selectedCount M)) :
    expand M v (indexEmbedding M j) = v j := by
  simp [expand, indexEmbedding]

theorem expand_test {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M) (b : Fin n → Fin 2) :
    expand M (fun j => if j ∈ restrictTest M T then some (bits M b j) else none) =
      fun i => if i ∈ T then some (b i) else none := by
  funext i
  by_cases hi : i ∈ M
  · have he : indexEmbedding M ((selectedIndex M).symm ⟨i,hi⟩) = i := by simp [indexEmbedding]
    simp only [expand, dif_pos hi, mem_restrictTest, bits, he]
  · have ht : i ∉ T := fun h => hi (hT h)
    simp [expand, hi, ht]

def restoreOutput {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (o : RawProtocol.Output (selectedCount M)) : RawProtocol.Output n where
  transcript := ⟨θ, BB84SiftingRandomness.bobBases θ M, liftTest M o.transcript.tested,
    expand M o.transcript.aliceTest, expand M o.transcript.bobTest, o.transcript.accepted⟩
  aliceKey := expand M o.aliceKey
  bobKey := expand M o.bobKey

theorem restore_output {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M)
    (θ : Fin n → BB84Basis) (b c : Fin n → Fin 2) (minKey tolerance : Nat) :
    restoreOutput M θ (RawProtocol.output (bases M θ) (bases M θ) (bits M b) (bits M c)
      (restrictTest M T) minKey tolerance) =
    RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance := by
  have ha : expand M
      (RawProtocol.output (bases M θ) (bases M θ) (bits M b) (bits M c)
        (restrictTest M T) minKey tolerance).aliceKey =
      (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance).aliceKey := by
    funext i
    by_cases hi : i ∈ M
    · obtain ⟨j,hj⟩ := (selectedIndex M).surjective ⟨i,hi⟩
      have he : indexEmbedding M j = i := congrArg Subtype.val hj
      rw [← he, expand_index]
      exact (private_keys M T hT θ b c minKey tolerance j).1.symm
    · simp [expand, hi, RawProtocol.output, RawProtocol.keyPositions,
        BB84SiftingRandomness.matched_bob]
  have hb : expand M
      (RawProtocol.output (bases M θ) (bases M θ) (bits M b) (bits M c)
        (restrictTest M T) minKey tolerance).bobKey =
      (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b c T minKey tolerance).bobKey := by
    funext i
    by_cases hi : i ∈ M
    · obtain ⟨j,hj⟩ := (selectedIndex M).surjective ⟨i,hi⟩
      have he : indexEmbedding M j = i := congrArg Subtype.val hj
      rw [← he, expand_index]
      exact (private_keys M T hT θ b c minKey tolerance j).2.symm
    · simp [expand, hi, RawProtocol.output, RawProtocol.keyPositions,
        BB84SiftingRandomness.matched_bob]
  change RawProtocol.Output.mk _ _ _ = RawProtocol.Output.mk _ _ _
  congr 1
  · change RawProtocol.PublicRecord.mk θ _ (liftTest M (restrictTest M T)) _ _ _ =
      RawProtocol.PublicRecord.mk θ _ T _ _ _
    dsimp only [RawProtocol.output]
    rw [lift_restrict M T hT, expand_test M T hT b, expand_test M T hT c,
      ← accepts_eq M T hT θ b c minKey tolerance]

end
end Foundation.Quantum.QKD.BB84SiftedInput
