import Foundation.Crypto.Semantics.Probability.FiniteRecoveryRigidity
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitExperiment

/-! A full-support five-state edge in the existing cipher grid has different
atom masses at its ends. No marginal-preserving forward kernel on these five
states has an exact left inverse, independently of coupling or local loss. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity
open Foundation.Probability
open scoped ENNReal
noncomputable section

def chain : Fin 4 → OrderedGridVertex 32 :=
  ![⟨![1,2,3],by decide⟩,⟨![1,2,4],by decide⟩,
    ⟨![2,2,4],by decide⟩,⟨![2,3,4],by decide⟩]
def source : OrderedGridVertex 32 := chain 0
def target : OrderedGridVertex 32 := chain 1

theorem chain_valid : gridChain 32 ![1,2,3] 4 chain := by
  intro t j
  fin_cases t <;> fin_cases j <;>
    norm_num [gridVertexCoordinate, gridCubeVertex, chain, cubeVertex, cubeAxisOrder]

theorem edge : faceEdge (orderedGridComplex 32) source target := by
  apply (orderedGridComplex_edge_iff 32 _ _).mpr
  refine ⟨?_,![1,2,3],4,chain,chain_valid,?_,?_⟩
  · intro same
    have h := congrArg (fun v : OrderedGridVertex 32 => (v.val 2).val) same
    change (3 : ℕ) = 4 at h
    omega
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩

theorem source_counts (key : Fin 5) : tableNaturalCounts source key = ![43,43,42,111,17] key := by
  fin_cases key <;> decide +kernel

theorem target_counts (key : Fin 5) : tableNaturalCounts target key = ![45,44,39,111,17] key := by
  fin_cases key <;> decide +kernel

def keyLaw (v : OrderedGridVertex 32) : PMF (Fin 5) :=
  (uniform (Fin 8 → Bool)).map (tableSampleEightBits v)

theorem key_atom (v : OrderedGridVertex 32) (key : Fin 5) :
    keyLaw v key = (tableNaturalCounts v key : ℝ≥0∞) / 256 := by
  calc
    _ = eventProb (keyLaw v) (· = key) := (PMF.toOuterMeasure_apply_singleton _ _).symm
    _ = _ := by rw [keyLaw,eventProb_map,tableSampleEightBits_probability]

theorem source_full (key : Fin 5) : key ∈ (keyLaw source).support := by
  rw [PMF.mem_support_iff,key_atom,source_counts]
  fin_cases key <;> norm_num

theorem target_full (key : Fin 5) : key ∈ (keyLaw target).support := by
  rw [PMF.mem_support_iff,key_atom,target_counts]
  fin_cases key <;> norm_num

theorem unmatched_atom (key : Fin 5) :
    (keyLaw source key).toReal ≠ (keyLaw target 0).toReal := by
  rw [key_atom,key_atom,source_counts,target_counts]
  fin_cases key <;> norm_num

theorem no_exact_recoverable_transport :
    ¬ ∃ (forward reverse : Fin 5 → PMF (Fin 5)),
      (keyLaw source).bind forward = keyLaw target ∧
      ∀ key, (forward key).bind reverse = PMF.pure key := by
  rintro ⟨forward,reverse,preserve,recovers⟩
  obtain ⟨e,masses⟩ := KernelRecovery.equal_card_preserving_atom
    (keyLaw source) (keyLaw target) forward reverse rfl preserve recovers
  have h := masses (e.symm 0)
  rw [e.apply_symm_apply] at h
  exact unmatched_atom (e.symm 0) (congrArg ENNReal.toReal h.symm)

theorem not_every_edge_exactly_recoverable :
    ¬ ∀ u v : OrderedGridVertex 32, faceEdge (orderedGridComplex 32) u v →
      ∃ (forward reverse : Fin 5 → PMF (Fin 5)),
        (keyLaw u).bind forward = keyLaw v ∧
        ∀ key, (forward key).bind reverse = PMF.pure key := by
  intro all_edges
  exact no_exact_recoverable_transport (all_edges source target edge)

theorem joint_law_factor (v : OrderedGridVertex 32) (message : Bool) :
    tableEightBitLaw v message = (keyLaw v).map (fun key => (key,tableEncryptBit v key message)) := by
  rw [keyLaw, PMF.map_comp]
  rfl

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity
