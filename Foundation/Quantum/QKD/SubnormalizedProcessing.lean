import Foundation.Quantum.QKD.SubnormalizedGuess
import Foundation.Quantum.BasisChannel

/-! Physical processing of the quantum blocks of a subnormalized CQ state.
The public/classical register is retained and no acceptance normalization is used. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {a b : Space}

/-- A channel on the second system; the first register is untouched. -/
def rightChannel (r : Space) (C : Channel a b) : Channel (.tensor r a) (.tensor r b) :=
  ((BasisChannel.channel (Equiv.prodComm r.Basis a.Basis)).seq (C.amplify r)).seq
    (BasisChannel.channel (Equiv.prodComm b.Basis r.Basis))

theorem rightChannel_entry (r : Space) (C : Channel a b) (A : Operator (.tensor r a))
    (s t : r.Basis) (u v : b.Basis) :
    (rightChannel r C).toKraus.apply A (s,u) (t,v) =
      C.toKraus.apply (A.submatrix (fun i => (s,i)) (fun j => (t,j))) u v := by
  unfold rightChannel
  simp only [Channel.seq, Kraus.seq_apply, BasisChannel.apply, BasisTransport.operator,
    Matrix.submatrix_apply]
  change (C.toKraus.amplify r).apply (A.submatrix Prod.swap Prod.swap) (u,s) (v,t) = _
  rw [Kraus.amplify_apply_entry]
  simp only [Kraus.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Prod.swap_prod_mk, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm

theorem post_physical [DecidableEq X] (ρ : State X a) (C : Channel a b) :
    joint (post ρ C) = (rightChannel (.register (Fintype.card X)) C).toKraus.apply (joint ρ) := by
  ext ⟨s,u⟩ ⟨t,v⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective s
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective t
  rw [joint_block, rightChannel_entry]
  have hs : (joint ρ).submatrix (fun i => (Fintype.equivFin X x,i))
      (fun j => (Fintype.equivFin X y,j)) = if x = y then ρ.block x else 0 := by
    ext i j
    simpa only [Matrix.submatrix_apply, Matrix.ite_apply, Matrix.zero_apply] using
      joint_block ρ x y i j
  rw [hs]
  by_cases h : x = y
  · simp only [h, ite_true, post]
  · simp only [h, ite_false]
    change 0 = C.toKraus.linear 0 u v
    rw [map_zero]
    rfl

end
end Foundation.Quantum.QKD.Subnormalized
