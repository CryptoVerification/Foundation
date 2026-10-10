import Foundation.Quantum.NuclearMass
import Foundation.Quantum.TraceAlgebra
import Mathlib.Analysis.Normed.Module.Basic

/-! A representation-independent nuclear norm on actual trace-class operators.
The infimum is over all absolutely summable rank-one expansions. Completeness
and the identification with the spectral trace norm are separate obligations. -/
namespace Foundation.Quantum.Infinite.TraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def representationCosts (T : TraceClass E) : Set ℝ :=
  {r | ∃ S : NuclearSeries E E, S.operator = T.operator ∧ S.mass = r}

omit [CompleteSpace E] in
theorem costs_nonempty (T : TraceClass E) : T.representationCosts.Nonempty := by
  obtain ⟨S,hS⟩ := T.representable
  exact ⟨S.mass,S,hS,rfl⟩

omit [CompleteSpace E] in
theorem costs_bddBelow (T : TraceClass E) : BddBelow T.representationCosts :=
  ⟨0, fun _ ⟨S,_,hs⟩ => hs ▸ S.mass_nonneg⟩

def nuclearNorm (T : TraceClass E) : ℝ := sInf T.representationCosts

omit [CompleteSpace E] in
theorem nuclearNorm_nonneg (T : TraceClass E) : 0 ≤ T.nuclearNorm :=
  le_csInf T.costs_nonempty (fun _ ⟨S,_,hs⟩ => hs ▸ S.mass_nonneg)

omit [CompleteSpace E] in
theorem nuclearNorm_le_mass (T : TraceClass E) (S : NuclearSeries E E) (hS : S.operator = T.operator) :
    T.nuclearNorm ≤ S.mass := csInf_le T.costs_bddBelow ⟨S,hS,rfl⟩

omit [CompleteSpace E] in
theorem exists_near_representation (T : TraceClass E) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : NuclearSeries E E, S.operator = T.operator ∧ S.mass < T.nuclearNorm + ε := by
  obtain ⟨r,⟨S,hS,hs⟩,hr⟩ := exists_lt_of_csInf_lt T.costs_nonempty (lt_add_of_pos_right _ hε)
  exact ⟨S,hS,hs ▸ hr⟩

omit [CompleteSpace E] in
theorem operator_norm_le (T : TraceClass E) : ‖T.operator‖ ≤ T.nuclearNorm := by
  apply le_csInf T.costs_nonempty
  rintro r ⟨S,hS,rfl⟩
  rw [← hS]
  exact S.norm_operator_le

theorem trace_norm_le (T : TraceClass E) : ‖T.trace‖ ≤ T.nuclearNorm := by
  apply le_csInf T.costs_nonempty
  rintro r ⟨S,hS,rfl⟩
  have he : T.trace = S.traceExpression :=
    (T.trace_congr (ofSeries S) hS.symm).trans (trace_ofSeries S)
  rw [he]
  exact S.trace_norm_le_mass

theorem nuclearNorm_zero : (0 : TraceClass E).nuclearNorm = 0 := by
  apply le_antisymm _ (nuclearNorm_nonneg _)
  have h := nuclearNorm_le_mass (0 : TraceClass E) (NuclearSeries.single 0 0) (by simp)
  simpa only [NuclearSeries.mass_single, norm_zero, zero_mul] using h

theorem nuclearNorm_eq_zero_iff (T : TraceClass E) : T.nuclearNorm = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply TraceClass.ext
    apply norm_eq_zero.mp
    exact le_antisymm (h ▸ T.operator_norm_le) (norm_nonneg _)
  · rintro rfl
    exact nuclearNorm_zero

theorem nuclearNorm_add_le (S T : TraceClass E) :
    (S + T).nuclearNorm ≤ S.nuclearNorm + T.nuclearNorm := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨X,hX,hx⟩ := S.exists_near_representation (half_pos hε)
  obtain ⟨Y,hY,hy⟩ := T.exists_near_representation (half_pos hε)
  have hxy := (S+T).nuclearNorm_le_mass (X.add Y) (by
    rw [NuclearSeries.add_operator, hX, hY, operator_add])
  rw [NuclearSeries.mass_add] at hxy
  linarith

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Transfer a representation bound to the infimum; the transformation need not choose a fixed representation. -/
theorem nuclearNorm_transfer_le (T : TraceClass E) (U : TraceClass F) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ S : NuclearSeries E E, S.operator = T.operator →
      ∃ R : NuclearSeries F F, R.operator = U.operator ∧ R.mass ≤ c * S.mass) :
    U.nuclearNorm ≤ c * T.nuclearNorm := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd : 0 < c + 1 := by linarith
  have heq : (c+1) * (ε / (c+1)) = ε := mul_div_cancel₀ ε (ne_of_gt hd)
  obtain ⟨S,hS,hs⟩ := T.exists_near_representation (div_pos hε hd)
  obtain ⟨R,hR,hr⟩ := h S hS
  have hu := U.nuclearNorm_le_mass R hR
  have hh := mul_le_mul_of_nonneg_left hs.le hc
  have hδ : 0 < ε / (c+1) := div_pos hε hd
  nlinarith

theorem nuclearNorm_smul_le (c : ℂ) (T : TraceClass E) :
    (c • T).nuclearNorm ≤ ‖c‖ * T.nuclearNorm := by
  apply nuclearNorm_transfer_le T (c • T) ‖c‖ (norm_nonneg c)
  intro S hS
  refine ⟨S.scale c, ?_, (S.mass_scale c).le⟩
  rw [NuclearSeries.scale_operator, hS, operator_smul]

theorem nuclearNorm_smul (c : ℂ) (T : TraceClass E) :
    (c • T).nuclearNorm = ‖c‖ * T.nuclearNorm := by
  by_cases hc : c = 0
  · simp [hc, nuclearNorm_zero]
  · apply le_antisymm (nuclearNorm_smul_le c T)
    have h := nuclearNorm_smul_le c⁻¹ (c • T)
    rw [inv_smul_smul₀ hc, norm_inv] at h
    have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h' := mul_le_mul_of_nonneg_left h hn.le
    have he : ‖c‖ * (‖c‖⁻¹ * (c • T).nuclearNorm) = (c • T).nuclearNorm := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul]
    rwa [he] at h'

instance : Norm (TraceClass E) := ⟨nuclearNorm⟩

theorem normedCore : NormedSpace.Core ℂ (TraceClass E) where
  norm_nonneg := nuclearNorm_nonneg
  norm_eq_zero_iff := nuclearNorm_eq_zero_iff
  norm_smul := nuclearNorm_smul
  norm_triangle := nuclearNorm_add_le

instance : NormedAddCommGroup (TraceClass E) := NormedAddCommGroup.ofCore normedCore
instance : NormedSpace ℂ (TraceClass E) := NormedSpace.ofCore normedCore

omit [CompleteSpace E] in
/-- The rank-one norm agrees with the product of the vector norms. -/
theorem norm_rankOne (x y : E) : ‖ofSeries (NuclearSeries.single x y)‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm
  · exact ((ofSeries (NuclearSeries.single x y)).nuclearNorm_le_mass _ rfl).trans_eq
      (NuclearSeries.mass_single x y)
  · calc
      _ = ‖InnerProductSpace.rankOne ℂ x y‖ := (InnerProductSpace.norm_rankOne x y).symm
      _ = ‖(ofSeries (NuclearSeries.single x y)).operator‖ :=
        congrArg norm (NuclearSeries.single_operator x y).symm
      _ ≤ _ := (ofSeries (NuclearSeries.single x y)).operator_norm_le

/-- The trace is now an actual continuous linear functional with norm at most one. -/
def traceContinuous : TraceClass E →L[ℂ] ℂ := traceLinear.mkContinuous 1 (fun T => by
  change ‖T.trace‖ ≤ 1 * T.nuclearNorm
  simpa only [one_mul] using T.trace_norm_le)

/-- The inclusion in bounded operators is continuous for the new norm, not an inherited operator-norm topology. -/
def inclusionContinuous : TraceClass E →L[ℂ] E →L[ℂ] E :=
  inclusion.mkContinuous 1 (fun T => by
    change ‖T.operator‖ ≤ 1 * T.nuclearNorm
    simpa only [one_mul] using T.operator_norm_le)

end
end Foundation.Quantum.Infinite.TraceClass
