import Foundation.Quantum.QKD.BB84KeyState
import Foundation.Quantum.BasisChannel
import Foundation.Quantum.LocalOperations

/-! Move the middle tensor factor to the end, retaining arbitrary entanglement.
Local operations on the first and last factors are transported explicitly. -/
namespace Foundation.Quantum.TensorExchange
noncomputable section
set_option backward.isDefEq.respectTransparency false

def equivalence (a e b : Space) :
    (Space.tensor (.tensor a e) b).Basis ≃ (Space.tensor (.tensor a b) e).Basis where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem operation (a e b : Space) (V : Operator a) (U : Operator b) :
    Op.tensor (Op.tensor V U) (Op.ident e) * Op.basisMap (equivalence a e b) =
      Op.basisMap (equivalence a e b) * Op.tensor (Op.tensor V (Op.ident e)) U := by
  change Op.seq (Op.basisMap (equivalence a e b)) (Op.tensor (Op.tensor V U) (Op.ident e)) =
    Op.seq (Op.tensor (Op.tensor V (Op.ident e)) U) (Op.basisMap (equivalence a e b))
  rw [Op.basisMap_seq, Op.seq_basisEquiv]
  ext ⟨⟨i,k⟩,u⟩ ⟨⟨j,v⟩,l⟩
  change (V i j * U k l) * (Op.ident e) u v = (V i j * (Op.ident e) u v) * U k l
  ring

/-- Naturality of the physical transport, before any product-input or
independence assumption. Isometries are required only to form the channels. -/
theorem local_operations (a e b : Space) (V : Operator a) (U : Operator b)
    (hV : V.conjTranspose*V = 1) (hU : U.conjTranspose*U = 1)
    (ρ : Operator (.tensor (.tensor a e) b)) :
    (BasisChannel.channel (equivalence a e b)).toKraus.apply
      (((Channel.ofIsometry (Op.tensor V (Op.ident e)) (QKD.tensor_isometry _ _ hV (by simp [Op.ident]))).amplify b).toKraus.apply
        ((Channel.ofIsometry (Op.tensor (Op.ident (.tensor a e)) U)
          (QKD.tensor_isometry _ _ (by simp [Op.ident]) hU)).toKraus.apply ρ)) =
    (((Channel.ofIsometry (Op.tensor V U) (QKD.tensor_isometry _ _ hV hU)).amplify e).toKraus.apply
      ((BasisChannel.channel (equivalence a e b)).toKraus.apply ρ)) := by
  simp only [BasisChannel.channel, Channel.ofIsometry, Channel.amplify,
    Kraus.amplify, Kraus.single, Kraus.apply, Fintype.sum_unique]
  have hc := Op.tensor_local_right (Op.tensor V (Op.ident e)) U
  have h := operation a e b V U
  calc
    _ = (Op.basisMap (equivalence a e b) *
          (Op.tensor (Op.tensor V (Op.ident e)) (Op.ident b) * Op.tensor (Op.ident (.tensor a e)) U)) *
        ρ * (Op.basisMap (equivalence a e b) *
          (Op.tensor (Op.tensor V (Op.ident e)) (Op.ident b) * Op.tensor (Op.ident (.tensor a e)) U)).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Op.tensor (Op.tensor V U) (Op.ident e) * Op.basisMap (equivalence a e b)) * ρ *
        (Op.tensor (Op.tensor V U) (Op.ident e) * Op.basisMap (equivalence a e b)).conjTranspose := by rw [hc, ← h]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end
end Foundation.Quantum.TensorExchange
