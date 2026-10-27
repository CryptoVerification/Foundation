/- Checkpoint 2026-10-28: the full build has not completed.
The user requested a checkpoint; the exhaustive neighbor check was interrupted.
This file is a proof candidate, not a completed validation artifact. -/
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitBoundary
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitNeighborChecks

/-! Kernel-checked finite separation on the actual N=32 grid edges.
Distances retain the secret key label; they are not adversarial advantage. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators
noncomputable section
open EightBitTable

theorem cubeVertex_monotone_step (o : Fin 6) (s t : Fin 4) (hst : s.val ≤ t.val) (j : Fin 3) :
    cubeVertex o s j ≤ cubeVertex o t j := by
  obtain ⟨r, hr⟩ := (cubeAxisOrder_bijective o).2 j
  rw [← hr, cubeVertex_order_coordinate, cubeVertex_order_coordinate]
  split_ifs <;> norm_num at * <;> omega

theorem gridChain_nat_difference (n : ℕ) (hn : 0 < n) (base : Fin 3 → Fin n)
    (o : Fin 6) (v : Fin 4 → OrderedGridVertex n) (hv : gridChain n base o v)
    (s t : Fin 4) (hst : s.val ≤ t.val) (j : Fin 3) :
    ((v s).val j).val ≤ ((v t).val j).val ∧
      ((v t).val j).val ≤ ((v s).val j).val+1 := by
  have hreal : (gridIntegralCoordinate (v s) j : ℝ) ≤ (gridIntegralCoordinate (v t) j : ℝ) := by
    rw [gridChain_integral_coordinate n hn base o v hv,
      gridChain_integral_coordinate n hn base o v hv]
    linarith [cubeVertex_monotone_step o s t hst j]
  have hlo : gridIntegralCoordinate (v s) j ≤ gridIntegralCoordinate (v t) j := by exact_mod_cast hreal
  have hhi := gridChain_coordinate_width n hn base o v hv t s j
  change (((v s).val j).val : ℤ) ≤ (((v t).val j).val : ℤ) at hlo
  change (((v t).val j).val : ℤ) ≤ (((v s).val j).val : ℤ)+1 at hhi
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

theorem neighbor_mask_exists (d : Fin 3 → ℕ) (hd : ∀ j, d j ≤ 1) :
    ∃ mask : Fin 8, ∀ j, neighborIncrement mask j = d j := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  refine ⟨⟨d 0+2*d 1+4*d 2, by omega⟩, ?_⟩
  intro j
  fin_cases j <;> dsimp [neighborIncrement] <;> omega

theorem table_chain_oriented_distance (base : Fin 3 → Fin 32) (o : Fin 6)
    (v : Fin 4 → OrderedGridVertex 32) (hv : gridChain 32 base o v)
    (s t : Fin 4) (hst : s.val ≤ t.val) :
    (∑ k : Fin 5, |tableCounts (v s) k-tableCounts (v t) k|) ≤ 148 := by
  let d := fun j => ((v t).val j).val-((v s).val j).val
  have hd (j : Fin 3) : d j ≤ 1 := by
    have h := gridChain_nat_difference 32 (by omega) base o v hv s t hst j
    dsimp [d]
    omega
  obtain ⟨mask, hmask⟩ := neighbor_mask_exists d hd
  have hidx (j : Fin 3) : ((v s).val j).val+neighborIncrement mask j = ((v t).val j).val := by
    rw [hmask j]
    have h := gridChain_nat_difference 32 (by omega) base o v hv s t hst j
    dsimp [d]
    omega
  have hc := neighbors_checked ((v s).val 0) ((v s).val 1) ((v s).val 2)
    (v s).property.1 (v s).property.2 mask
  dsimp only [neighborCheck] at hc
  rw [hidx 0, hidx 1, hidx 2] at hc
  have htop : ((v t).val 2).val ≤ 32 := Nat.le_of_lt_succ ((v t).val 2).isLt
  exact hc (v t).property.1 (v t).property.2 htop

theorem table_chain_distance (base : Fin 3 → Fin 32) (o : Fin 6)
    (v : Fin 4 → OrderedGridVertex 32) (hv : gridChain 32 base o v) (s t : Fin 4) :
    (∑ k : Fin 5, |tableCounts (v s) k-tableCounts (v t) k|) ≤ 148 := by
  rcases le_total s.val t.val with h | h
  · exact table_chain_oriented_distance base o v hv s t h
  · calc
      _ = ∑ k : Fin 5, |tableCounts (v t) k-tableCounts (v s) k| :=
        Finset.sum_congr rfl (fun k _ => abs_sub_comm _ _)
      _ ≤ 148 := table_chain_oriented_distance base o v hv t s h

theorem table_five_key_edge_upper (u w : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u w) (message : Bool) :
    jointTV (tableFiveCipher u).toCipher (tableFiveCipher w).toCipher message ≤ 37 / 128 := by
  obtain ⟨_, base, o, v, hv, hu, hw⟩ := (orderedGridComplex_edge_iff 32 u w).mp he
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hu
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hw
  rw [← hs, ← ht]
  exact eight_bit_jointTV_le (tableCounts (v s)) (tableCounts (v t))
    (table_vertex_checked (v s)).1 (table_vertex_checked (v s)).2.1
    (table_vertex_checked (v t)).1 (table_vertex_checked (v t)).2.1
    (table_chain_distance base o v hv s t) message

theorem table_five_key_implementation_upper (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) :
    implementationDistance (tableFiveCipher u).toCipher (tableFiveCipher v).toCipher ≤ 37 / 128 :=
  max_le (table_five_key_edge_upper u v he false) (table_five_key_edge_upper u v he true)

/-- The finite five-key table is strictly smoother on some actual edge than
every perfect four-key assignment preserving its first-four-key boundary. -/
theorem table_perfect_separation (d : OrderedGridVertex 32 → PerfectCipher (Fin 4))
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (d v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      jointTV (tableFiveCipher u).toCipher (tableFiveCipher v).toCipher message <
        jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨u, v, he, hd⟩ := table_four_key_obstruction d hb
  refine ⟨u, v, he, ?_⟩
  intro message
  have hu := table_five_key_edge_upper u v he message
  have hl := hd message
  linarith

/-- The strict gap persists under the stated four-key error budget. -/
theorem table_approximate_separation (c : OrderedGridVertex 32 → Cipher (Fin 4))
    (ε δ : OrderedGridVertex 32 → ℝ)
    (h0 : ∀ v, ∑ k, (c v).weight k * error0 (c v) k ≤ δ v)
    (h1 : ∀ v, ∑ k, (c v).weight k * error1 (c v) k ≤ δ v)
    (hp : ∀ v, |bias (signedContrast (c v))| ≤ ε v)
    (hm : ∀ v, ε v+2*δ v ≤ 1 / 8)
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      repair (signedContrast (c v)) = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      implementationDistance (tableFiveCipher u).toCipher (tableFiveCipher v).toCipher+1 / 384 ≤
        implementationDistance (c u) (c v) := by
  obtain ⟨u, v, he, hl⟩ := table_approximate_four_key_obstruction c ε δ h0 h1 hp hm hb
  refine ⟨u, v, he, ?_⟩
  have hu := table_five_key_implementation_upper u v he
  linarith

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
