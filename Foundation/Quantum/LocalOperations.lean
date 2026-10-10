import Foundation.Quantum.States

/-! Local operations on different factors commute as interpreted maps on all
joint operators. Kraus indices and derivation trees need not be equal. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Op
variable {a b r : Space}

theorem tensor_local_right (M : Op a b) (U : Operator r) :
    Op.tensor M (Op.ident r) * Op.tensor (Op.ident a) U = Op.tensor M U := by
  unfold Op.tensor Op.ident Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem tensor_right_local (M : Op a b) (U : Operator r) :
    Op.tensor (Op.ident b) U * Op.tensor M (Op.ident r) = Op.tensor M U := by
  unfold Op.tensor Op.ident Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

end Op

namespace Kraus
variable {a b r : Space}

/-- A general local Kraus map commutes with conjugating the retained system.
No product-state assumption is made about the input operator. -/
theorem commute_right (K : Kraus a b) (U : Operator r) (ρ : Operator (.tensor a r)) :
    (K.amplify r).apply ((Op.tensor (Op.ident a) U)*ρ*(Op.tensor (Op.ident a) U).conjTranspose) =
      (Op.tensor (Op.ident b) U)*((K.amplify r).apply ρ)*(Op.tensor (Op.ident b) U).conjTranspose := by
  simp only [apply, amplify, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (Op.tensor (K.operator k) (Op.ident r) * Op.tensor (Op.ident a) U) * ρ *
        (Op.tensor (K.operator k) (Op.ident r) * Op.tensor (Op.ident a) U).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Op.tensor (Op.ident b) U * Op.tensor (K.operator k) (Op.ident r)) * ρ *
        (Op.tensor (Op.ident b) U * Op.tensor (K.operator k) (Op.ident r)).conjTranspose := by
      rw [Op.tensor_local_right, Op.tensor_right_local]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Kraus
end
end Foundation.Quantum
