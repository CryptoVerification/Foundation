import Foundation.Quantum.Instrument
import Foundation.Quantum.Distinguishability
import Foundation.Quantum.Category

/-! Concrete physical channels and the bridge from coherent operations. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

/-- A coherent isometry induces the corresponding conjugation channel. -/
theorem isometry_lift_seq {a b c : Space} (M : Op a b) (N : Op b c)
    (hM : M.conjTranspose * M = 1) (hN : N.conjTranspose * N = 1) :
    (N * M).conjTranspose * (N * M) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N.conjTranspose,
    hN, Matrix.one_mul, hM]

theorem mix_isometry : Op.mix.conjTranspose * Op.mix = 1 := by
  ext i j
  change (∑ k : Fin 2, star (Op.mix k i) * Op.mix k j) = if i = j then 1 else 0
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [Op.mix, Space.Basis, Space.basisDecidableEq, Complex.ext_iff]

def mixChannel : Channel .bit .bit := Channel.ofIsometry Op.mix mix_isometry

def projector (a : Space) (r : a.Basis) : Op a a :=
  fun i j => if i = r ∧ j = r then 1 else 0

theorem projector_complete (a : Space) :
    (∑ r, (projector a r).conjTranspose * projector a r) = (1 : Op a a) := by
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, projector,
    Matrix.one_apply, ite_and, mul_ite, eq_comm]

def basisEffect (a : Space) (r : a.Basis) : Effect a where
  matrix := projector a r
  positive := by
    have h : projector a r = Matrix.diagonal (fun i => if i = r then (1 : ℂ) else 0) := by
      ext i j
      by_cases hi : i = r <;> by_cases hj : j = r <;>
        simp_all [projector, Matrix.diagonal_apply, eq_comm]
    rw [h]
    exact Matrix.PosSemidef.diagonal (by intro i; dsimp; split_ifs <;> simp)
  complement_positive := by
    have h : (1 : Op a a) - projector a r =
        Matrix.diagonal (fun i => if i = r then (0 : ℂ) else 1) := by
      ext i j
      by_cases hi : i = r <;> by_cases hj : j = r <;>
        simp_all [projector, Matrix.diagonal_apply, Matrix.one_apply, eq_comm]
    rw [h]
    exact Matrix.PosSemidef.diagonal (by intro i; dsimp; split_ifs <;> simp)

def basisInstrument (a : Space) : Instrument a a (Fintype.card a.Basis) where
  branch r := Kraus.single (projector a ((Fintype.equivFin a.Basis).symm r))
  complete := by
    simp only [Kraus.single_effect]
    exact (Equiv.sum_comp (Fintype.equivFin a.Basis).symm
      (fun r => (projector a r).conjTranspose * projector a r)).trans (projector_complete a)

/-- Dephasing forgets the basis outcome, unlike the previous amplitude-level erase. -/
def dephase (a : Space) : Channel a a where
  index := a.Basis
  finite := inferInstance
  operator := projector a
  complete := projector_complete a

/-- The entire auxiliary density matrix is retained, including quantum correlations. -/
theorem dephase_amplify_apply (a e : Space) (ρ : Operator (.tensor a e))
    (i j : a.Basis × e.Basis) :
    ((dephase a).amplify e).toKraus.apply ρ i j = if i.1 = j.1 then ρ i j else 0 := by
  simp [Kraus.apply, Channel.amplify, Kraus.amplify, dephase, projector, Op.tensor,
    Op.ident, Matrix.kronecker, Matrix.kroneckerMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Space.Basis, ite_and,
    ite_mul, mul_ite, eq_comm, -Finset.sum_boole]
  by_cases h : i.1 = j.1 <;> simp [h, apply_ite]

/-- Dephasing twice is indistinguishable from dephasing once, for any auxiliary system. -/
theorem dephase_idempotent (a : Space) :
    Approx ((dephase a).seq (dephase a)) (dephase a) 0 := by
  intro e ρ E
  have h : ((((dephase a).seq (dephase a)).amplify e).run ρ).matrix =
      (((dephase a).amplify e).run ρ).matrix := by
    rw [Channel.amplify_seq_run_matrix]
    ext i j
    change ((dephase a).amplify e).apply _ i j = ((dephase a).amplify e).apply _ i j
    rw [dephase_amplify_apply, dephase_amplify_apply]
    change (if i.1 = j.1 then ((dephase a).amplify e).apply ρ.matrix i j else 0) = _
    rw [dephase_amplify_apply]
    split_ifs <;> rfl
  unfold Effect.probability
  rw [h]
  simp

end
end Foundation.Quantum
