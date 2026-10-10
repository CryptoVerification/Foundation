import Foundation.Quantum.PartialTrace

/-! Finite Stinespring dilation of a represented channel. The environment
remains explicit, and tracing it out recovers the original operator map. -/
namespace Foundation.Quantum.Channel
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

/-- Kraus labels become an actual quantum environment register. -/
def dilation (C : Channel a b) : Op a (.tensor b (.register (Fintype.card C.index))) :=
  fun i j => C.operator ((Fintype.equivFin C.index).symm i.2) i.1 j

theorem dilation_gram (C : Channel a b) : C.dilation.conjTranspose * C.dilation = 1 := by
  ext i j
  change (∑ p : b.Basis × Fin (Fintype.card C.index),
    star (C.operator ((Fintype.equivFin C.index).symm p.2) p.1 i) *
      C.operator ((Fintype.equivFin C.index).symm p.2) p.1 j) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h : (∑ k : C.index, ∑ l : b.Basis,
      star (C.operator k l i) * C.operator k l j) = (1 : Operator a) i j := by
    simpa only [Kraus.effect, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply] using congrFun (congrFun C.complete i) j
  exact (Equiv.sum_comp (Fintype.equivFin C.index).symm
    (fun k => ∑ l : b.Basis, star (C.operator k l i) * C.operator k l j)).trans h

def dilated (C : Channel a b) : Channel a (.tensor b (.register (Fintype.card C.index))) :=
  Channel.ofIsometry C.dilation C.dilation_gram

theorem discard_dilation (C : Channel a b) (ρ : Operator a) :
    (discardRight b (.register (Fintype.card C.index))).toKraus.apply
      (C.dilated.toKraus.apply ρ) = C.toKraus.apply ρ := by
  ext i j
  rw [discardRight_apply]
  simp only [dilated, Channel.ofIsometry, Kraus.single_apply]
  change (∑ k : Fin (Fintype.card C.index),
    (C.dilation * ρ * C.dilation.conjTranspose) (i, k) (j, k)) = _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dilation]
  exact (Equiv.sum_comp (Fintype.equivFin C.index).symm
    (fun k => (C.operator k * ρ * (C.operator k).conjTranspose) i j)).trans (by
      simp only [Kraus.apply, Matrix.sum_apply])

end
end Foundation.Quantum.Channel
