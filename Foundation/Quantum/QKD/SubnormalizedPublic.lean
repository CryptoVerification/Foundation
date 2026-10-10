import Foundation.Quantum.QKD.SubnormalizedGuess

/-! Public classical information retained beside a subnormalized quantum
state. The original branch weight is preserved for arbitrary joint measurements. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open Guessing
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X L : Type} [Fintype X] [Fintype L] {e : Space}

def withPublic (ρ : State (X × L) e) : State X (publicSpace L e) where
  block x := ∑ l, Matrix.kronecker
    (basisDensity (.register (Fintype.card L)) (Fintype.equivFin L l)).matrix (ρ.block (x,l))
  positive x := Matrix.posSemidef_sum _ (fun l _ =>
    (basisDensity _ _).positive.kronecker (ρ.positive (x,l)))
  bounded := by
    unfold Matrix.kronecker
    simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized,
      one_mul, Complex.re_sum]
    simpa only [Fintype.sum_prod_type] using ρ.bounded

theorem mass_withPublic (ρ : State (X × L) e) : mass (withPublic ρ) = mass ρ := by
  unfold mass withPublic Matrix.kronecker
  simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized,
    one_mul, Complex.re_sum, Fintype.sum_prod_type]

theorem withPublic_ofCQ (ρ : CQ (X × L) e) :
    withPublic (ofCQ ρ) = ofCQ (Guessing.withPublic ρ) := rfl

def leakScore (ρ : State (X × L) e) (M : L → Measurement X e) : ℝ :=
  ∑ l, ∑ x, ((M l).operator x * ρ.block (x,l)).trace.re

theorem score_withPublic (ρ : State (X × L) e) (M : Measurement X (publicSpace L e)) :
    score (withPublic ρ) M = leakScore ρ (readMeasurement M) := by
  unfold score withPublic leakScore readMeasurement
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg Complex.re (trace_classical_block _ _ _)

theorem score_jointMeasurement (ρ : State (X × L) e) (M : L → Measurement X e) :
    score (withPublic ρ) (jointMeasurement M) = leakScore ρ M := by
  rw [score_withPublic]
  unfold leakScore
  simp_rw [read_joint_operator]

/-- Public-dependent strategies are actual joint measurements; this theorem
retains the event's original weight. -/
theorem leakScore_le_probability (ρ : State (X × L) e) (M : L → Measurement X e) :
    leakScore ρ M ≤ probability (withPublic ρ) := by
  rw [← score_jointMeasurement]
  exact score_le_probability _ _

variable [Nonempty X]

/-- Conversely, every arbitrary joint measurement is a public-dependent
strategy, so the joint optimum is exactly the supremum of those strategies. -/
theorem public_probability (ρ : State (X × L) e) :
    probability (withPublic ρ) = sSup (Set.range (leakScore ρ)) := by
  classical
  have hn : (Set.range (leakScore ρ)).Nonempty :=
    ⟨_,⟨fun _ => constantMeasurement (Classical.arbitrary X),rfl⟩⟩
  have hb : BddAbove (Set.range (leakScore ρ)) :=
    ⟨_,fun _ ⟨M,hM⟩ => hM ▸ leakScore_le_probability ρ M⟩
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    intro q hq
    obtain ⟨M,rfl⟩ := hq
    rw [score_withPublic]
    exact le_csSup hb ⟨_,rfl⟩
  · exact csSup_le hn (fun _ ⟨M,hM⟩ => hM ▸ leakScore_le_probability ρ M)

theorem public_probability_le_mass (ρ : State (X × L) e) :
    probability (withPublic ρ) ≤ mass ρ := by
  simpa only [mass_withPublic] using probability_le_mass (withPublic ρ)

/-- Selecting an event cannot increase weighted guessing success, even
when the event is correlated with the private value and the quantum system. -/
theorem public_restrict_le (ρ : State (X × L) e) (P : X × L → Prop) [DecidablePred P] :
    probability (withPublic (restrict ρ P)) ≤ probability (withPublic ρ) := by
  apply csSup_le (range_nonempty _)
  intro q hq
  obtain ⟨M,rfl⟩ := hq
  apply le_trans _ (score_le_probability (withPublic ρ) M)
  rw [score_withPublic, score_withPublic]
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P (x,l)
  · simp [restrict, hp]
  · simpa [restrict, hp] using (Complex.nonneg_iff.mp
      (trace_product_nonneg ((readMeasurement M l).positive x) (ρ.positive (x,l)))).1

end
end Foundation.Quantum.QKD.Subnormalized
