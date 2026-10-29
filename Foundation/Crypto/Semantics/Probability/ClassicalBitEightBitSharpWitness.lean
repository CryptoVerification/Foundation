import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitBoundary

/-! An actual grid edge attaining the proposed five-key upper bound.
This witness does not depend on the exhaustive neighbor certificate.
The distance includes the secret key label, not merely the ciphertext. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section

def sharpTableChain : Fin 4 → OrderedGridVertex 32 :=
  ![⟨![0, 8, 24], by decide⟩,
    ⟨![0, 8, 25], by decide⟩,
    ⟨![1, 8, 25], by decide⟩,
    ⟨![1, 9, 25], by decide⟩]

theorem sharpTableChain_valid : gridChain 32 ![0, 8, 24] 4 sharpTableChain := by
  intro t j
  fin_cases t <;> fin_cases j <;>
    norm_num [gridVertexCoordinate, gridCubeVertex, sharpTableChain, cubeVertex, cubeAxisOrder]

theorem sharpTableChain_edge :
    faceEdge (orderedGridComplex 32) (sharpTableChain 0) (sharpTableChain 2) := by
  apply (orderedGridComplex_edge_iff 32 _ _).mpr
  refine ⟨?_, ![0, 8, 24], 4, sharpTableChain, sharpTableChain_valid, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun v : OrderedGridVertex 32 => (v.val 0).val) h
    change (0 : ℕ) = 1 at hh
    omega
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩

theorem sharpTableChain_count_distance :
    (∑ k : Fin 5, |tableCounts (sharpTableChain 0) k -
      tableCounts (sharpTableChain 2) k|) = 148 := by
  decide +kernel

theorem sharpTableChain_jointTV (message : Bool) :
    jointTV (tableFiveCipher (sharpTableChain 0)).toCipher
      (tableFiveCipher (sharpTableChain 2)).toCipher message = 37 / 128 := by
  rw [perfect_jointTV]
  change l1Distance (dyadicVector 256 (tableCounts (sharpTableChain 0)))
    (dyadicVector 256 (tableCounts (sharpTableChain 2))) / 2 = 37 / 128
  rw [dyadic_l1_exact 256 (by omega), sharpTableChain_count_distance]
  norm_num

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
