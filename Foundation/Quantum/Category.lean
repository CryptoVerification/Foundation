import Foundation.Quantum.Finite
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! The matrix operations form a genuine symmetric monoidal category. The
coherence maps are linear extensions of equivalences of basis index types. -/
namespace Foundation.Quantum
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[reducible] instance matrixCategory : Category Space where
  Hom := Op
  id := Op.ident
  comp := Op.seq
  id_comp := Op.ident_seq
  comp_id := Op.seq_ident
  assoc := Op.seq_assoc

namespace Op
variable {a b c : Space}

theorem basisMap_seq (h : a.Basis → b.Basis) (M : Op b c) :
    seq (basisMap h) M = fun i j => M i (h j) := by
  ext i j
  simp [seq, basisMap, Matrix.mul_apply]

theorem seq_basisEquiv (M : Op a b) (h : b.Basis ≃ c.Basis) :
    seq M (basisMap h) = fun i j => M (h.symm i) j := by
  ext i j
  simp [seq, basisMap, Matrix.mul_apply, ← h.symm_apply_eq]

theorem basisMap_id (a : Space) : basisMap (id : a.Basis → a.Basis) = ident a := rfl

def basisIso {a b : Space} (e : a.Basis ≃ b.Basis) : a ≅ b where
  hom := basisMap e
  inv := basisMap e.symm
  hom_inv_id := by
    change seq (basisMap e) (basisMap e.symm) = ident a
    rw [basisMap_seq]
    ext i j
    simp [basisMap, ident, Matrix.one_apply]
  inv_hom_id := by
    change seq (basisMap e.symm) (basisMap e) = ident b
    rw [basisMap_seq]
    ext i j
    simp [basisMap, ident, Matrix.one_apply]

theorem dagger_basisIso {a b : Space} (e : a.Basis ≃ b.Basis) :
    dagger (basisIso e).hom = (basisIso e).inv := by
  ext i j
  simp [basisIso, dagger, basisMap, Matrix.conjTranspose_apply, e.eq_symm_apply, eq_comm]

theorem tensor_ident (a b : Space) : tensor (ident a) (ident b) = ident (.tensor a b) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [tensor, ident, Matrix.one_apply, ite_and]
  split_ifs <;> rfl

theorem dagger_tensor {a b c d} (f : Op a b) (g : Op c d) :
    dagger (tensor f g) = tensor (dagger f) (dagger g) := by
  ext i j
  simp [dagger, tensor, Matrix.conjTranspose_apply]
end Op

@[reducible] instance matrixMonoidalStruct : MonoidalCategoryStruct Space where
  tensorObj := Space.tensor
  tensorUnit := .unit
  tensorHom := Op.tensor
  whiskerLeft a _ _ f := Op.tensor (Op.ident a) f
  whiskerRight f a := Op.tensor f (Op.ident a)
  associator a b c := Op.basisIso (Equiv.prodAssoc a.Basis b.Basis c.Basis)
  leftUnitor a := Op.basisIso (Equiv.uniqueProd a.Basis Unit)
  rightUnitor a := Op.basisIso (Equiv.prodUnique a.Basis Unit)

instance matrixMonoidal : MonoidalCategory Space where
  toMonoidalCategoryStruct := matrixMonoidalStruct
  tensorHom_def := by
    intro a b c d f g
    change Op.tensor f g = Op.seq (Op.tensor f (Op.ident c)) (Op.tensor (Op.ident b) g)
    rw [← Op.tensor_seq]
    simp
  id_tensorHom_id := Op.tensor_ident
  tensorHom_comp_tensorHom := by
    intro a b c d e z f h g k
    exact (Op.tensor_seq f g h k).symm
  whiskerLeft_id := Op.tensor_ident
  id_whiskerRight := Op.tensor_ident
  associator_naturality := by
    intro a b c d e z f g h
    change Op.seq (Op.tensor (Op.tensor f g) h)
      (Op.basisMap (Equiv.prodAssoc d.Basis e.Basis z.Basis)) =
      Op.seq (Op.basisMap (Equiv.prodAssoc a.Basis b.Basis c.Basis))
        (Op.tensor f (Op.tensor g h))
    rw [Op.seq_basisEquiv, Op.basisMap_seq]
    ext i j
    simp [Op.tensor, mul_assoc]
  leftUnitor_naturality := by
    intro a b f
    change Op.seq (Op.tensor (Op.ident .unit) f)
      (Op.basisMap (Equiv.uniqueProd b.Basis Unit)) =
      Op.seq (Op.basisMap (Equiv.uniqueProd a.Basis Unit)) f
    rw [Op.seq_basisEquiv, Op.basisMap_seq]
    ext i j
    simp [Op.tensor, Op.ident]
  rightUnitor_naturality := by
    intro a b f
    change Op.seq (Op.tensor f (Op.ident .unit))
      (Op.basisMap (Equiv.prodUnique b.Basis Unit)) =
      Op.seq (Op.basisMap (Equiv.prodUnique a.Basis Unit)) f
    rw [Op.seq_basisEquiv, Op.basisMap_seq]
    ext i j
    simp [Op.tensor, Op.ident]
  pentagon := by
    intro a b c d
    change Op.seq (Op.tensor (Op.assoc a b c) (Op.ident d))
      (Op.seq (Op.assoc a (.tensor b c) d) (Op.tensor (Op.ident a) (Op.assoc b c d))) =
      Op.seq (Op.assoc (.tensor a b) c d) (Op.assoc a b (.tensor c d))
    ext i j
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.assoc, Op.basisMap,
      Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Space.Basis]
    rcases i with ⟨i1, i2, i3, i4⟩
    rcases j with ⟨⟨⟨j1, j2⟩, j3⟩, j4⟩
    simp [Prod.mk.injEq, ite_and]
    split_ifs <;> simp_all
  triangle := by
    intro a b
    change Op.seq (Op.assoc a .unit b) (Op.tensor (Op.ident a) (Op.unleft b)) =
      Op.tensor (Op.unright a) (Op.ident b)
    ext i j
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.assoc, Op.unleft, Op.unright, Op.basisMap,
      Matrix.mul_apply, Matrix.one_apply, Space.Basis]

instance matrixBraided : BraidedCategory Space where
  braiding a b := Op.basisIso (Equiv.prodComm a.Basis b.Basis)
  braiding_naturality_right := by
    intro a b c f
    change Op.seq (Op.tensor (Op.ident a) f)
      (Op.basisMap (Equiv.prodComm a.Basis c.Basis)) =
      Op.seq (Op.basisMap (Equiv.prodComm a.Basis b.Basis))
        (Op.tensor f (Op.ident a))
    rw [Op.seq_basisEquiv, Op.basisMap_seq]
    ext i j
    exact mul_comm _ _
  braiding_naturality_left := by
    intro a b f c
    change Op.seq (Op.tensor f (Op.ident c))
      (Op.basisMap (Equiv.prodComm b.Basis c.Basis)) =
      Op.seq (Op.basisMap (Equiv.prodComm a.Basis c.Basis))
        (Op.tensor (Op.ident c) f)
    rw [Op.seq_basisEquiv, Op.basisMap_seq]
    ext i j
    exact mul_comm _ _
  hexagon_forward := by
    intro a b c
    change Op.seq (Op.assoc a b c) (Op.seq (Op.swap a (.tensor b c)) (Op.assoc b c a)) =
      Op.seq (Op.tensor (Op.swap a b) (Op.ident c))
        (Op.seq (Op.assoc b a c) (Op.tensor (Op.ident b) (Op.swap a c)))
    ext i j
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.assoc, Op.swap, Op.basisMap,
      Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Space.Basis]
    rcases i with ⟨i1, i2, i3⟩
    rcases j with ⟨⟨j1, j2⟩, j3⟩
    simp [Prod.mk.injEq, ite_and]
    split_ifs <;> simp_all
  hexagon_reverse := by
    intro a b c
    change Op.seq (Op.basisMap (Equiv.prodAssoc a.Basis b.Basis c.Basis).symm)
      (Op.seq (Op.swap (.tensor a b) c)
        (Op.basisMap (Equiv.prodAssoc c.Basis a.Basis b.Basis).symm)) =
      Op.seq (Op.tensor (Op.ident a) (Op.swap b c))
        (Op.seq (Op.basisMap (Equiv.prodAssoc a.Basis c.Basis b.Basis).symm)
          (Op.tensor (Op.swap a c) (Op.ident b)))
    ext i j
    simp [-Finset.sum_boole, Op.seq, Op.tensor, Op.ident, Op.swap, Op.basisMap,
      Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Space.Basis, Equiv.prodAssoc]
    rcases i with ⟨⟨i1, i2⟩, i3⟩
    rcases j with ⟨j1, j2, j3⟩
    simp [Prod.mk.injEq, ite_and]
    split_ifs <;> simp_all

theorem swap_symmetry (a b : Space) :
    Op.seq (Op.swap a b) (Op.swap b a) = Op.ident (.tensor a b) := by
  unfold Op.swap
  rw [Op.basisMap_seq]
  ext i j
  simp [Op.basisMap, Op.ident, Matrix.one_apply]

instance matrixSymmetric : SymmetricCategory Space where
  toBraidedCategory := matrixBraided
  symmetry a b := swap_symmetry a b

end
end Foundation.Quantum
