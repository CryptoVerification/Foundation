import Foundation.Quantum.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! Bundled compact and classical structures of the concrete finite model.
The self-duality uses a selected basis; it is not a canonical identification
of an arbitrary Hilbert space with its dual. -/
namespace Foundation.Quantum
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

instance matrixPairing (a : Space) : ExactPairing a a where
  coevaluation' := Op.cup a
  evaluation' := Op.cap a
  coevaluation_evaluation' := by
    change Op.seq (Op.tensor (Op.ident a) (Op.cup a))
      (Op.seq (Op.basisIso (Equiv.prodAssoc a.Basis a.Basis a.Basis)).inv
        (Op.tensor (Op.cap a) (Op.ident a))) =
      Op.seq (Op.unright a) (Op.basisIso (Equiv.uniqueProd a.Basis Unit)).inv
    apply Matrix.ext
    intro ⟨⟨⟩, i⟩ ⟨j, ⟨⟩⟩
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.basisIso, Op.basisMap,
      Op.unright, Op.cup, Op.cap, Op.dagger, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Space.Basis, Equiv.prodAssoc, Equiv.uniqueProd, eq_comm]
  evaluation_coevaluation' := by
    change Op.seq (Op.tensor (Op.cup a) (Op.ident a))
      (Op.seq (Op.assoc a a a) (Op.tensor (Op.ident a) (Op.cap a))) =
      Op.seq (Op.unleft a) (Op.basisIso (Equiv.prodUnique a.Basis Unit)).inv
    apply Matrix.ext
    intro ⟨i, ⟨⟩⟩ ⟨⟨⟩, j⟩
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.basisIso, Op.basisMap,
      Op.assoc, Op.unleft, Op.cup, Op.cap, Op.dagger, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Space.Basis, Equiv.prodUnique, eq_comm]

instance matrixRigid : RigidCategory Space where
  rightDual a := { rightDual := a }
  leftDual a := { leftDual := a }

/-- The compatibility required by Heunen 3.2.9, in the chosen self-dual basis. -/
theorem dagger_compact (a : Space) :
    Op.seq (Op.dagger (Op.cap a)) (Op.swap a a) = Op.cup a := by
  rw [Op.cap, Op.dagger_dagger, Op.cup_copy, Op.seq_assoc, Op.copy_comm]

/-- Definition 3.3.4 with explicit associators and unitors. -/
structure ClassicalStructure (a : Space) where
  delta : Op a (.tensor a a)
  nu : Op a .unit
  coassoc : Op.seq (Op.seq delta (Op.tensor delta (Op.ident a))) (Op.assoc a a a) =
    Op.seq delta (Op.tensor (Op.ident a) delta)
  cocomm : Op.seq delta (Op.swap a a) = delta
  leftCounit : Op.seq delta
    (Op.seq (Op.tensor nu (Op.ident a)) (Op.unleft a)) = Op.ident a
  rightCounit : Op.seq delta
    (Op.seq (Op.tensor (Op.ident a) nu) (Op.unright a)) = Op.ident a
  special : Op.seq delta (Op.dagger delta) = Op.ident a
  frobenius : Op.seq (Op.dagger delta) delta =
    Op.seq (Op.seq (Op.tensor (Op.ident a) delta) (Op.dagger (Op.assoc a a a)))
      (Op.tensor (Op.dagger delta) (Op.ident a))

/-- Example 3.3.5: all the fields are proved for the standard orthonormal basis. -/
def standardClassical (a : Space) : ClassicalStructure a where
  delta := Op.copy a
  nu := Op.erase a
  coassoc := Op.copy_coassoc a
  cocomm := Op.copy_comm a
  leftCounit := Op.copy_leftErase a
  rightCounit := Op.copy_rightErase a
  special := Op.copy_special a
  frobenius := Op.copy_frobenius a

/-- The source's notion of measurement, not a probabilistic instrument. -/
def IsMeasurement {a b : Space} (m : Op a b) : Prop :=
  Op.seq (Op.dagger m) m = Op.ident b

theorem mix_isMeasurement : IsMeasurement Op.mix := Op.mix_dagger_epi

end
end Foundation.Quantum
