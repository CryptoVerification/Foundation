import Foundation.Quantum.QKD.Subnormalized
import Foundation.Quantum.RecordObservation

/-! Subnormalized branches are real positive joint operators produced by a
specified trace-decreasing Kraus filter. Their mass is the probability of the
recorded event in the original normalized state, without conditional division. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open Guessing
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {e : Space}

def joint (ρ : State X e) : Operator (.tensor (.register (Fintype.card X)) e) :=
  ∑ x, Matrix.kronecker
    (basisDensity (.register (Fintype.card X)) (Fintype.equivFin X x)).matrix (ρ.block x)

theorem joint_positive (ρ : State X e) : (joint ρ).PosSemidef :=
  Matrix.posSemidef_sum _ (fun x _ => (basisDensity _ _).positive.kronecker (ρ.positive x))

theorem joint_trace (ρ : State X e) : (joint ρ).trace.re = mass ρ := by
  unfold joint Matrix.kronecker
  simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized,
    one_mul, Complex.re_sum, mass]

theorem joint_trace_complex (ρ : State X e) : (joint ρ).trace = (mass ρ : ℂ) := by
  apply Complex.ext
  · simpa using joint_trace ρ
  · simpa using (Complex.nonneg_iff.mp (joint_positive ρ).trace_nonneg).2.symm

theorem joint_ofCQ (ρ : CQ X e) : joint (ofCQ ρ) = ρ.density.matrix := rfl

theorem joint_block [DecidableEq X] (ρ : State X e) (x y : X) (i j : e.Basis) :
    joint ρ (Fintype.equivFin X x,i) (Fintype.equivFin X y,j) =
      if x = y then ρ.block x i j else 0 := by
  by_cases h : x = y
  · subst y
    simp [joint, basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.diagonal_apply]
  · simp [joint, basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.diagonal_apply, h]

/-- A concrete selective Kraus operation: retain only labels satisfying P. -/
def eventFilter (P : X → Prop) [DecidablePred P] :
    Kraus (.tensor (.register (Fintype.card X)) e) (.tensor (.register (Fintype.card X)) e) :=
  Kraus.single (recordEvent e (fun t => P ((Fintype.equivFin X).symm t))).matrix

theorem restrict_physical (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    joint (restrict ρ P) = (eventFilter P).apply (joint ρ) := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective s
  rw [joint_block]
  simp only [eventFilter, Kraus.single_apply, recordEvent, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.symm_apply_apply]
  rw [joint_block]
  by_cases h : x = y
  · subst y
    by_cases hp : P x <;> simp [hp, restrict]
  · simp [h]

/-- Event mass equals the ordinary physical measurement probability. -/
theorem restrict_mass_probability (ρ : CQ X e) (P : X → Prop) [DecidablePred P] :
    mass (restrict (ofCQ ρ) P) =
      (recordEvent e (fun t => P ((Fintype.equivFin X).symm t))).probability ρ.density := by
  classical
  rw [mass_restrict, recordEvent_probability, ← (Fintype.equivFin X).sum_comp]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x
  · simp only [hp, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [CQ.density_block]
    simp [ofCQ]
  · simp [hp]

end
end Foundation.Quantum.QKD.Subnormalized
