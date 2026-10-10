import Foundation.Quantum.QKD.CQRelabel

/-! A public classical register can be included in the quantum side system.
Arbitrary joint measurements have exactly the same optimal guessing power
as a family of measurements selected after reading that public register. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X L : Type} [Fintype X] [Fintype L] {e : Space}

abbrev publicSpace (L : Type) [Fintype L] (e : Space) :=
  Space.tensor (.register (Fintype.card L)) e

/-- Retain the classical public value as an orthogonal register beside Eve. -/
def withPublic (ρ : CQ (X × L) e) : CQ X (publicSpace L e) where
  block x := ∑ l, Matrix.kronecker
    (basisDensity (.register (Fintype.card L)) (Fintype.equivFin L l)).matrix (ρ.block (x,l))
  positive x := Matrix.posSemidef_sum _ (fun l _ =>
    (basisDensity _ _).positive.kronecker (ρ.positive (x,l)))
  normalized := by
    unfold Matrix.kronecker
    simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized, one_mul]
    simpa only [Fintype.sum_prod_type] using ρ.normalized

/-- Read a public diagonal block of an arbitrary joint guessing measurement. -/
def readMeasurement (M : Measurement X (publicSpace L e)) (l : L) : Measurement X e where
  operator x := (M.operator x).submatrix (fun i => (Fintype.equivFin L l,i))
    (fun i => (Fintype.equivFin L l,i))
  positive x := (M.positive x).submatrix _
  complete := by
    ext i j
    have h := congrFun (congrFun M.complete (Fintype.equivFin L l,i)) (Fintype.equivFin L l,j)
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply, Prod.mk.injEq,
      true_and] using h

/-- Pairing with a classical diagonal quantum state reads exactly the
corresponding diagonal block of a completely general joint operator. -/
theorem trace_classical_block (M : Operator (publicSpace L e)) (l : L) (B : Operator e) :
    (M * Matrix.kronecker (basisDensity (.register (Fintype.card L)) (Fintype.equivFin L l)).matrix B).trace =
      ((M.submatrix (fun i => (Fintype.equivFin L l,i))
        (fun i => (Fintype.equivFin L l,i))) * B).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    basisDensity, Matrix.kronecker, Matrix.kroneckerMap, Matrix.diagonal_apply,
    Matrix.submatrix_apply, mul_ite, -Finset.sum_boole]

/-- A joint measurement may have off-diagonal public blocks. Those blocks
contribute zero, so reading the public value first loses no guessing power. -/
theorem score_withPublic (ρ : CQ (X × L) e) (M : Measurement X (publicSpace L e)) :
    score (withPublic ρ) M = leakScore ρ (readMeasurement M) := by
  unfold score withPublic leakScore readMeasurement
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg Complex.re (trace_classical_block _ _ _)

/-- Any measurement on the joint register is bounded by the public-dependent optimum. -/
theorem withPublic_le (ρ : CQ (X × L) e) :
    guessingProbability (withPublic ρ) ≤ leakedGuessingProbability ρ := by
  apply (guessingProbability_le_iff _ _).mpr
  intro M
  rw [score_withPublic]
  exact leakScore_le_optimal _ _

/-- A family selected by the public value becomes one joint quantum measurement. -/
def publicOperator (M : L → Measurement X e) (x : X) : Operator (publicSpace L e) :=
  ∑ l, Matrix.kronecker
    (basisDensity (.register (Fintype.card L)) (Fintype.equivFin L l)).matrix ((M l).operator x)

theorem publicOperator_block [DecidableEq L] (M : L → Measurement X e)
    (x : X) (l m : L) (i j : e.Basis) :
    publicOperator M x (Fintype.equivFin L l,i) (Fintype.equivFin L m,j) =
      if l = m then (M l).operator x i j else 0 := by
  by_cases h : l = m
  · subst m
    simp [publicOperator, basisDensity, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.diagonal_apply]
  · simp [publicOperator, basisDensity, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.diagonal_apply, h]

def jointMeasurement (M : L → Measurement X e) : Measurement X (publicSpace L e) where
  operator := publicOperator M
  positive x := Matrix.posSemidef_sum _ (fun l _ =>
    (basisDensity _ _).positive.kronecker ((M l).positive x))
  complete := by
    classical
    ext ⟨r,i⟩ ⟨s,j⟩
    obtain ⟨l,rfl⟩ := (Fintype.equivFin L).surjective r
    obtain ⟨m,rfl⟩ := (Fintype.equivFin L).surjective s
    simp only [Matrix.sum_apply, Matrix.one_apply,
      Prod.mk.injEq, Equiv.apply_eq_iff_eq]
    have hb (x : X) := publicOperator_block M x l m i j
    simp_rw [hb]
    by_cases h : l = m
    · subst m
      simp only [ite_true, true_and]
      simpa only [Matrix.sum_apply, Matrix.one_apply] using congrFun (congrFun (M l).complete i) j
    · simp [h]

theorem read_joint_operator (M : L → Measurement X e) (l : L) (x : X) :
    (readMeasurement (jointMeasurement M) l).operator x = (M l).operator x := by
  classical
  ext i j
  change publicOperator M x _ _ = _
  rw [publicOperator_block]
  simp

theorem score_jointMeasurement (ρ : CQ (X × L) e) (M : L → Measurement X e) :
    score (withPublic ρ) (jointMeasurement M) = leakScore ρ M := by
  rw [score_withPublic]
  unfold leakScore
  simp_rw [read_joint_operator]

/-- No restriction on joint quantum measurements is introduced by treating
an orthogonal public register as a classical measurement selector. -/
theorem withPublic_optimal (ρ : CQ (X × L) e) :
    guessingProbability (withPublic ρ) = leakedGuessingProbability ρ := by
  apply le_antisymm (withPublic_le ρ)
  apply csSup_le (leak_range_nonempty ρ)
  intro q hq
  obtain ⟨M,rfl⟩ := hq
  rw [← score_jointMeasurement]
  exact score_le_guessingProbability _ _

end
end Foundation.Quantum.QKD.Guessing
