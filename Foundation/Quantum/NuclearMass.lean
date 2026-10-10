import Foundation.Quantum.NuclearAlgebra

/-! Quantitative bounds for nuclear representations. These are bounds on a
representation; the operator norm introduced later takes the infimum over
all representations of the same actual operator. -/
namespace Foundation.Quantum.Infinite.NuclearSeries
noncomputable section
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def mass (S : NuclearSeries E F) : ℝ := ∑' n, ‖S.left n‖ * ‖S.right n‖

omit [CompleteSpace E] [CompleteSpace F] in
theorem mass_nonneg (S : NuclearSeries E F) : 0 ≤ S.mass := tsum_nonneg (fun _ => by positivity)

omit [CompleteSpace E] [CompleteSpace F] in
theorem mass_single (x : F) (y : E) : (single x y).mass = ‖x‖ * ‖y‖ := by
  simp [mass, single, apply_ite]

omit [CompleteSpace E] [CompleteSpace F] in
theorem mass_scale (S : NuclearSeries E F) (c : ℂ) : (S.scale c).mass = ‖c‖ * S.mass := by
  simp only [mass, scale, norm_smul, mul_assoc]
  exact tsum_mul_left

omit [CompleteSpace E] [CompleteSpace F] in
theorem mass_add (S T : NuclearSeries E F) : (S.add T).mass = S.mass + T.mass := by
  let f : ℕ ⊕ ℕ → ℝ := Sum.elim
    (fun n => ‖S.left n‖ * ‖S.right n‖) (fun n => ‖T.left n‖ * ‖T.right n‖)
  have hs : HasSum f (S.mass + T.mass) := HasSum.sum S.summable.hasSum T.summable.hasSum
  have he : (S.add T).mass = ∑' n, f (Equiv.natSumNatEquivNat.symm n) := by
    apply tsum_congr
    intro n
    dsimp only [add]
    cases Equiv.natSumNatEquivNat.symm n <;> rfl
  exact he.trans ((Equiv.natSumNatEquivNat.symm.tsum_eq f).trans hs.tsum_eq)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem mass_post_le (S : NuclearSeries E F) (A : F →L[ℂ] G) :
    (S.post A).mass ≤ ‖A‖ * S.mass := by
  simp only [mass]
  rw [← tsum_mul_left]
  exact (S.post A).summable.tsum_le_tsum (by
    intro n
    dsimp [post]
    nlinarith [mul_le_mul_of_nonneg_right (A.le_opNorm (S.left n)) (norm_nonneg (S.right n))])
    (S.summable.mul_left ‖A‖)

omit [CompleteSpace F] in
theorem mass_pre_le (S : NuclearSeries E F) (A : G →L[ℂ] E) :
    (S.pre A).mass ≤ ‖A‖ * S.mass := by
  change (∑' n, ‖S.left n‖ * ‖A.adjoint (S.right n)‖) ≤ ‖A‖ * S.mass
  rw [mass, ← tsum_mul_left]
  apply (S.pre A).summable.tsum_le_tsum _ (S.summable.mul_left ‖A‖)
  intro n
  have hb := A.adjoint.le_opNorm (S.right n)
  rw [ContinuousLinearMap.adjoint.norm_map] at hb
  change ‖S.left n‖ * ‖A.adjoint (S.right n)‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (S.left n))]

omit [CompleteSpace E] in
theorem trace_norm_le_mass (S : NuclearSeries E E) : ‖S.traceExpression‖ ≤ S.mass := by
  apply (norm_tsum_le_tsum_norm S.summable_trace.norm).trans
  exact S.summable_trace.norm.tsum_le_tsum (fun n => by
    simpa only [mul_comm] using norm_inner_le_norm (S.right n) (S.left n)) S.summable

end
end Foundation.Quantum.Infinite.NuclearSeries
