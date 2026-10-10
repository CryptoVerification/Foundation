import Foundation.Quantum.NuclearNorm
import Foundation.Quantum.NuclearFlatten
import Mathlib.Analysis.Normed.Group.Completeness

/-! Completeness of the nuclear ideal, proved by flattening near-minimal
representations of each term in an absolutely summable operator series.
The limit is an actual bounded operator with a nuclear representation. -/
namespace Foundation.Quantum.Infinite.TraceClass
noncomputable section
open Filter Finset
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Any absolutely summable series in the nuclear norm converges in that norm. -/
theorem summable_norm_imp_limit (u : ℕ → TraceClass E) (hu : Summable (fun n => ‖u n‖)) :
    ∃ T : TraceClass E, Tendsto (fun k => ∑ i ∈ range k, u i) atTop (𝓝 T) := by
  choose S hS hm using (fun n => (u n).exists_near_representation
    (show (0 : ℝ) < (1/2)^n by positivity))
  have hmass : Summable (fun n => (S n).mass) :=
    (hu.add summable_geometric_two).of_nonneg_of_le (fun n => (S n).mass_nonneg)
      (fun n => (hm n).le)
  let X := NuclearSeries.flatten S hmass
  let T : TraceClass E := ofSeries X
  refine ⟨T, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hbound (k : Nat) : ‖(∑ i ∈ range k, u i) - T‖ ≤ ∑' n, (S (n+k)).mass := by
    have htail : Summable (fun n => (S (n+k)).mass) := (summable_nat_add_iff k).mpr hmass
    let R := NuclearSeries.flatten (fun n => S (n+k)) htail
    have hop : (T - ∑ i ∈ range k, u i).operator = R.operator := by
      change T.operator - inclusion (∑ i ∈ range k, u i) = R.operator
      rw [map_sum]
      change X.operator - ∑ i ∈ range k, (u i).operator = R.operator
      rw [NuclearSeries.flatten_operator, NuclearSeries.flatten_operator]
      simp_rw [hS]
      have hs := (NuclearSeries.summable_operators S hmass).sum_add_tsum_nat_add k
      simp_rw [hS] at hs
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hs.symm)
    have he : T - ∑ i ∈ range k, u i = ofSeries R := TraceClass.ext hop
    rw [norm_sub_rev, he]
    change (ofSeries R).nuclearNorm ≤ _
    exact ((ofSeries R).nuclearNorm_le_mass R rfl).trans_eq
      (NuclearSeries.flatten_mass (fun n => S (n+k)) htail)
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (tendsto_sum_nat_add (fun n => (S n).mass))

instance : CompleteSpace (TraceClass E) :=
  NormedAddCommGroup.completeSpace_of_summable_imp_tendsto summable_norm_imp_limit

end
end Foundation.Quantum.Infinite.TraceClass
