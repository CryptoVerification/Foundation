import Foundation.Crypto.Logic.Polygraph.GeneralNativeCorrelatedRecovery
import Mathlib.Analysis.SpecificLimits.Basic

/-! An infinite-support semantic register: a geometric natural number paired
with the actual ciphertext. The register is retained, not resampled by the
lifted kernel. No bounded native generator for this infinite law is asserted. -/
namespace CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery
open Foundation.Probability GeneralNativeRecovery GeneralNativeRecoveryCells
open GeneralNativeCorrelatedRecovery CorrelatedGameFrames
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

def geometric : PMF Nat := ⟨fun n => ((2 : ℝ≥0∞)⁻¹) ^ (n + 1), by
  apply ENNReal.summable.hasSum_iff.mpr
  rw [ENNReal.tsum_geometric_add_one,ENNReal.one_sub_inv_two,inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

theorem geometric_supported (n : Nat) : n ∈ geometric.support := by
  apply (PMF.mem_support_iff _ _).mpr
  change ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) ≠ 0
  exact pow_ne_zero _ (by norm_num)

theorem geometric_support_infinite : geometric.support.Infinite := by
  have all : geometric.support = Set.univ := by ext n; simp only [Set.mem_univ,iff_true]; exact geometric_supported n
  rw [all]
  exact Set.infinite_univ

def context (ciphertext : Bool) : PMF (Nat × Bool) := geometric.map (fun n => (n,ciphertext))

theorem context_first (ciphertext : Bool) : (context ciphertext).map Prod.fst = geometric := by
  rw [context,PMF.map_comp]
  change geometric.map id = geometric
  exact PMF.map_id _

theorem source_first (message : Bool) (event : Fin 5 → Prop) :
    (sourceFrame message event context).law.map (fun pair => pair.2.1) = geometric := by
  change (((sourceGame message event).program.eval).bind (fun s =>
    (context (Machine.NativePreparedState.decode s).2).map (fun c => (s,c)))).map (fun pair => pair.2.1) = _
  rw [PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  change ((sourceGame message event).program.eval).bind
    (fun s => (context (Machine.NativePreparedState.decode s).2).map Prod.fst) = _
  simp_rw [context_first]
  exact PMF.bind_const _ _

theorem source_support_infinite (message : Bool) (event : Fin 5 → Prop) : (sourceFrame message event context).law.support.Infinite := by
  intro finite
  have projected : ((sourceFrame message event context).law.map (fun pair => pair.2.1)).support.Finite := by
    rw [PMF.support_map]
    exact finite.image _
  rw [source_first] at projected
  exact geometric_support_infinite projected

theorem source_ciphertext (message : Bool) (event : Fin 5 → Prop) (pair : State × (Nat × Bool))
    (supported : pair ∈ (sourceFrame message event context).law.support) : pair.2.2 = (Machine.NativePreparedState.decode pair.1).2 := by
  change pair ∈ ((sourceLaw message).bind (fun s =>
    (context (Machine.NativePreparedState.decode s).2).map (fun c => (s,c)))).support at supported
  obtain ⟨s,_,reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨label,labelSupported,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  change label ∈ (geometric.map (fun n => (n,(Machine.NativePreparedState.decode s).2))).support at labelSupported
  obtain ⟨n,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp labelSupported
  rfl

def infiniteCell (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) (test : Nat × Bool → Prop) :=
  framedCell r message beforePc afterPc event context test

def infiniteEdit (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) (test : Nat × Bool → Prop) :=
  framedEdit r message beforePc afterPc event context test

theorem infinite_lower (r : Fin 95) (message : Bool) (beforePc afterPc : Nat) (event : Fin 5 → Prop) (test : Nat × Bool → Prop) :
    ENNReal.ofReal (3 / 256 : ℝ) ≤ GeneralKernelVariation.distance ((sourceFrame message event context).observed test).program.eval
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (nativeStep r message beforePc afterPc event)) (native_compatible r message beforePc afterPc event context)).kernel
      (lift (sourceFrame message event context) (targetFrame message afterPc event context) test
        (.step (stationaryStep r message afterPc event)) (stationary_compatible r message afterPc event context)).kernel :=
  framed_lower r message beforePc afterPc event context test

end
end CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery
