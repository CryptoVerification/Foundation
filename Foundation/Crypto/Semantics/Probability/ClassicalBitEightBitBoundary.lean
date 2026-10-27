import Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicCertificate
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitVertices

/-! Interpret the kernel-checked N=32 table as five-key perfect ciphers.
Its first four boundary counts certify the fixed four-key obstruction. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
open EightBitTable

def tableCounts (v : OrderedGridVertex 32) (k : Fin 5) : ℤ :=
  counts (v.val 0).val (v.val 1).val (v.val 2).val k.val

theorem table_vertex_checked (v : OrderedGridVertex 32) :
    vertexCheck (v.val 0).val (v.val 1).val (v.val 2).val :=
  vertices_checked (v.val 0) (v.val 1) (v.val 2) v.property.1 v.property.2

def tableFiveCipher (v : OrderedGridVertex 32) : PerfectCipher (Fin 5) :=
  dyadicPerfectCipher 256 (by omega) (tableCounts v)
    (table_vertex_checked v).1 (table_vertex_checked v).2.1

def tableFourCounts (v : OrderedGridVertex 32) (k : Fin 4) : ℤ := tableCounts v k.castSucc

def tableFourVector (v : OrderedGridVertex 32) : Fin 4 → ℝ := dyadicVector 256 (tableFourCounts v)

theorem table_boundary_iff (v : OrderedGridVertex 32) :
    (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) ↔
      boundary (v.val 0).val (v.val 1).val (v.val 2).val := by
  constructor
  · rintro ⟨k, hk⟩
    rw [gridVertexPosition_numerator] at hk
    have hreal : (gridParameterNumerator 32 v k : ℝ) = 0 := by
      exact (div_eq_zero_iff.mp hk).resolve_right (by norm_num)
    have hi : gridParameterNumerator 32 v k = 0 := by exact_mod_cast hreal
    change (v.val 0).val = 0 ∨ (v.val 0).val = (v.val 1).val ∨
      (v.val 1).val = (v.val 2).val ∨ (v.val 2).val = 32
    fin_cases k <;> dsimp [gridParameterNumerator] at hi
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · intro h
    change (v.val 0).val = 0 ∨ (v.val 0).val = (v.val 1).val ∨
      (v.val 1).val = (v.val 2).val ∨ (v.val 2).val = 32 at h
    rcases h with h | h | h | h
    · refine ⟨0, ?_⟩
      rw [gridVertexPosition_numerator]
      have hi : gridParameterNumerator 32 v 0 = 0 := by dsimp [gridParameterNumerator]; omega
      simp [hi]
    · refine ⟨1, ?_⟩
      rw [gridVertexPosition_numerator]
      have hi : gridParameterNumerator 32 v 1 = 0 := by dsimp [gridParameterNumerator]; omega
      simp [hi]
    · refine ⟨2, ?_⟩
      rw [gridVertexPosition_numerator]
      have hi : gridParameterNumerator 32 v 2 = 0 := by dsimp [gridParameterNumerator]; omega
      simp [hi]
    · refine ⟨3, ?_⟩
      rw [gridVertexPosition_numerator]
      have hi : gridParameterNumerator 32 v 3 = 0 := by dsimp [gridParameterNumerator]; omega
      simp [hi]

theorem table_raw_grid (v : OrderedGridVertex 32) (k : Fin 4) :
    rawFour (v.val 0).val (v.val 1).val (v.val 2).val k = gridSharpNumerator 32 v k := by
  fin_cases k <;> dsimp [rawFour, gridSharpNumerator, gridParameterNumerator]

theorem table_boundary_error (v : OrderedGridVertex 32)
    (hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    l1Distance (tableFourVector v)
      (normalizeSigned (sharpAffine (gridVertexPosition 32 (by omega) v))) ≤ 1 / 64 := by
  have hc := (table_vertex_checked v).2.2 ((table_boundary_iff v).mp hv)
  have hL : 0 < ∑ k, |gridSharpNumerator 32 v k| := by
    simpa only [table_raw_grid v] using hc.2.1
  have he (k : Fin 4) :
      |tableFourCounts v k*(∑ j, |gridSharpNumerator 32 v j|)-gridSharpNumerator 32 v k*256| ≤
        ∑ j, |gridSharpNumerator 32 v j| := by
    simpa only [table_raw_grid v, tableFourCounts, tableCounts, Fin.val_castSucc] using hc.2.2 k
  exact grid_boundary_integer_error 32 (by omega) v (tableFourCounts v) hL he

theorem table_four_key_obstruction (d : OrderedGridVertex 32 → PerfectCipher (Fin 4))
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (d v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      2 / 3 ≤ jointTV (d u).toCipher (d v).toCipher message := by
  apply ordered_grid_perfect_edge 32 (by omega) d
  intro v hv
  rw [hb v hv]
  exact table_boundary_error v hv

theorem table_approximate_four_key_obstruction (c : OrderedGridVertex 32 → Cipher (Fin 4))
    (ε δ : OrderedGridVertex 32 → ℝ)
    (h0 : ∀ v, ∑ k, (c v).weight k * error0 (c v) k ≤ δ v)
    (h1 : ∀ v, ∑ k, (c v).weight k * error1 (c v) k ≤ δ v)
    (hp : ∀ v, |bias (signedContrast (c v))| ≤ ε v)
    (hm : ∀ v, ε v+2*δ v ≤ 1 / 8)
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      repair (signedContrast (c v)) = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      7 / 24 ≤ implementationDistance (c u) (c v) := by
  have hmargin (v : OrderedGridVertex 32) : ε v+2*δ v ≤ 1-(7 / 8 : ℝ) := by
    linarith [hm v]
  have he (v : OrderedGridVertex 32) (hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
      l1Distance (repair (signedContrast (c v)))
        (normalizeSigned (sharpAffine (gridVertexPosition 32 (by omega) v))) ≤ 1 / 64 := by
    rw [hb v hv]
    exact table_boundary_error v hv
  have h := ordered_grid_approximate_edge 32 (by omega) c ε δ (7 / 8) (by norm_num)
    h0 h1 hp hmargin he
  have hratio : (7 / 8 : ℝ)/3 = 7 / 24 := by norm_num
  rw [hratio] at h
  exact h

theorem table_boundary_counts_valid (v : OrderedGridVertex 32)
    (hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    (∑ k, tableFourCounts v k) = 0 ∧ (∑ k, |tableFourCounts v k|) = 256 := by
  have hc := table_vertex_checked v
  have hz : tableCounts v (Fin.last 4) = 0 := (hc.2.2 ((table_boundary_iff v).mp hv)).1
  have hs : (∑ k : Fin 5, tableCounts v k) = 0 := hc.1
  have hm : (∑ k : Fin 5, |tableCounts v k|) = 256 := hc.2.1
  rw [Fin.sum_univ_castSucc] at hs hm
  simp only [hz, abs_zero, add_zero] at hs hm
  exact ⟨hs, hm⟩

theorem table_five_boundary_correspondence (v : OrderedGridVertex 32)
    (hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    (∀ k : Fin 4, (tableFiveCipher v).signed k.castSucc = tableFourVector v k) ∧
      (tableFiveCipher v).signed (Fin.last 4) = 0 := by
  constructor
  · intro k; rfl
  · have hz : tableCounts v (Fin.last 4) = 0 :=
      ((table_vertex_checked v).2.2 ((table_boundary_iff v).mp hv)).1
    change (tableCounts v (Fin.last 4) : ℝ)/256 = 0
    rw [hz]
    norm_num

/-- A concrete four-key assignment with exactly the prescribed boundary.
Interior vertices use a fixed two-key pad, so the lower-bound family is nonempty. -/
def tableFourWitness (v : OrderedGridVertex 32) : PerfectCipher (Fin 4) := by
  classical
  by_cases hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0
  · exact dyadicPerfectCipher 256 (by omega) (tableFourCounts v)
      (table_boundary_counts_valid v hv).1 (table_boundary_counts_valid v hv).2
  · let c : Fin 4 → ℤ := fun k => if k.val = 0 then 128 else if k.val = 1 then -128 else 0
    exact dyadicPerfectCipher 256 (by omega) c (by decide) (by decide)

theorem table_four_witness_boundary (v : OrderedGridVertex 32)
    (hv : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    (tableFourWitness v).signed = tableFourVector v := by
  simp only [tableFourWitness, dif_pos hv]
  rfl

theorem table_four_boundary_realizable :
    ∃ d : OrderedGridVertex 32 → PerfectCipher (Fin 4),
      ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
        (d v).signed = tableFourVector v :=
  ⟨tableFourWitness, table_four_witness_boundary⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
