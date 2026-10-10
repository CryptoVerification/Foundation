import Foundation.Quantum.NuclearMass

/-! Countable sums of absolutely summable rank-one expansions are again
such expansions. Both the mass and actual operator are computed by justified
interchange of absolutely convergent sums. -/
namespace Foundation.Quantum.Infinite.NuclearSeries
noncomputable section
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem mass_double_summable (S : ℕ → NuclearSeries E F) (h : Summable (fun n => (S n).mass)) :
    Summable (fun p : ℕ × ℕ => ‖(S p.1).left p.2‖ * ‖(S p.1).right p.2‖) :=
  (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨fun n => (S n).summable,h⟩

def flatten (S : ℕ → NuclearSeries E F) (h : Summable (fun n => (S n).mass)) : NuclearSeries E F where
  left k := (S (Nat.pairEquiv.symm k).1).left (Nat.pairEquiv.symm k).2
  right k := (S (Nat.pairEquiv.symm k).1).right (Nat.pairEquiv.symm k).2
  summable := by
    let f : ℕ × ℕ → ℝ := fun p => ‖(S p.1).left p.2‖ * ‖(S p.1).right p.2‖
    exact (Nat.pairEquiv.symm.summable_iff (f := f)).mpr (mass_double_summable S h)

omit [CompleteSpace E] [CompleteSpace F] in
theorem flatten_mass (S : ℕ → NuclearSeries E F) (h : Summable (fun n => (S n).mass)) :
    (flatten S h).mass = ∑' n, (S n).mass := by
  change (∑' k, (fun p : ℕ × ℕ => ‖(S p.1).left p.2‖ * ‖(S p.1).right p.2‖) (Nat.pairEquiv.symm k)) = _
  exact (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ =>
    ‖(S p.1).left p.2‖ * ‖(S p.1).right p.2‖)).trans ((mass_double_summable S h).tsum_prod)

omit [CompleteSpace E] in
theorem summable_operators (S : ℕ → NuclearSeries E F) (h : Summable (fun n => (S n).mass)) :
    Summable (fun n => (S n).operator) := by
  apply Summable.of_norm
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (S n).norm_operator_le)

omit [CompleteSpace E] in
theorem flatten_operator (S : ℕ → NuclearSeries E F) (h : Summable (fun n => (S n).mass)) :
    (flatten S h).operator = ∑' n, (S n).operator := by
  let f : ℕ × ℕ → E →L[ℂ] F := fun p =>
    InnerProductSpace.rankOne ℂ ((S p.1).left p.2) ((S p.1).right p.2)
  have hf : Summable f := Summable.of_norm (by
    simpa only [f, InnerProductSpace.norm_rankOne] using mass_double_summable S h)
  change (∑' k, f (Nat.pairEquiv.symm k)) = ∑' n, ∑' m, f (n,m)
  rw [Nat.pairEquiv.symm.tsum_eq]
  exact hf.tsum_prod

end
end Foundation.Quantum.Infinite.NuclearSeries
